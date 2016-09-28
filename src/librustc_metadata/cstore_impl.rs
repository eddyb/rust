// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use cstore;
use encoder;
use locator;
use schema;

use rustc::middle::cstore::{InlinedItem, CrateStore, CrateSource, ExternCrate};
use rustc::middle::cstore::{NativeLibraryKind, LinkMeta, LinkagePreference};
use rustc::hir::def::{self, Def};
use rustc::middle::lang_items;
use rustc::mir::Mir;
use rustc::ty::{self, TyCtxt, Ty};
use rustc::ty::demand::{Provider, Unsupported};
use rustc::hir::def_id::{CrateNum, DefId, DefIndex, CRATE_DEF_INDEX};

use rustc::dep_graph::DepNode;
use rustc::hir::map as hir_map;
use rustc::hir::map::DefKey;
use rustc::util::nodemap::{NodeSet, DefIdMap};
use rustc_back::PanicStrategy;

use std::cell::RefCell;
use std::mem;
use std::path::PathBuf;
use std::rc::Rc;

use syntax::ast;
use syntax::attr;
use syntax::parse::token;
use rustc::hir::svh::Svh;
use rustc_back::target::Target;
use rustc::hir;

pub struct MetadataProvider {
    cstore: Rc<cstore::CStore>
}

impl MetadataProvider {
    pub fn new(cstore: Rc<cstore::CStore>) -> Self {
        MetadataProvider {
            cstore: cstore
        }
    }
}

macro_rules! handlers {
    ($def_id:ident, $cdata:ident <$lt:tt>
     $($name:ident in $tcx:ident.$map:ident -> $ty:ty $op:block)*) => {
        impl<$lt> Provider<$lt> for MetadataProvider {
            $(#[inline]
            fn $name<'a>(&self, $tcx: TyCtxt<'a, $lt, $lt>, $def_id: DefId)
                         -> Result<$ty, Unsupported> {
                if $def_id.is_local() {
                    return Err(Unsupported);
                }

                $tcx.dep_graph.read(DepNode::MetaData($def_id));

                let $cdata = self.cstore.get_crate_data($def_id.krate);
                let res = $op;
                $tcx.$map.borrow_mut().insert($def_id, Clone::clone(&res));
                Ok(res)
            })*
        }
    }
}

handlers! { def_id, cdata <'tcx>
    ty in tcx.item_types -> Ty<'tcx> {
        cdata.get_type(def_id.index, tcx)
    }
    generics in tcx.generics -> &'tcx ty::Generics<'tcx> {
        tcx.alloc_generics(cdata.get_generics(def_id.index, tcx))
    }
    predicates in tcx.predicates -> ty::GenericPredicates<'tcx> {
        cdata.get_predicates(def_id.index, tcx)
    }
    super_predicates in tcx.super_predicates -> ty::GenericPredicates<'tcx> {
        cdata.get_super_predicates(def_id.index, tcx)
    }
    trait_def in tcx.trait_defs -> &'tcx ty::TraitDef {
        tcx.alloc_trait_def(cdata.get_trait_def(def_id.index, tcx))
    }
    adt_def in tcx.adt_defs -> &'tcx ty::AdtDef {
        cdata.get_adt_def(def_id.index, tcx)
    }
    variances in tcx.item_variance_map -> Rc<Vec<ty::Variance>> {
        Rc::new(cdata.get_item_variances(def_id.index))
    }
    associated_item_def_ids in tcx.associated_item_def_ids -> Rc<Vec<DefId>> {
        let mut result = vec![];
        cdata.each_child_of_item(def_id.index, |child| result.push(child.def.def_id()));
        Rc::new(result)
    }
    associated_item in tcx.associated_items -> ty::AssociatedItem {
        cdata.get_associated_item(def_id.index)
    }
    impl_trait_ref in tcx.impl_trait_refs -> Option<ty::TraitRef<'tcx>> {
        cdata.get_impl_trait(def_id.index, tcx)
    }
    custom_coerce_unsized_kind in tcx.custom_coerce_unsized_kinds
            -> ty::adjustment::CustomCoerceUnsized {
        cdata.get_custom_coerce_unsized_kind(def_id.index).unwrap_or_else(|| {
            bug!("custom_coerce_unsized_kind: `{:?}` is missing its kind", def_id);
        })
    }
    mir in tcx.mir_map -> &'tcx RefCell<Mir<'tcx>> {
        let mir = cdata.maybe_get_item_mir(tcx, def_id.index).unwrap_or_else(|| {
            bug!("get_item_mir: missing MIR for `{:?}`", def_id)
        });

        let mir = tcx.alloc_mir(mir);

        // Perma-borrow MIR from extern crates to prevent mutation.
        mem::forget(mir.borrow());

        mir
    }
    closure_kind in tcx.closure_kinds -> ty::ClosureKind {
        cdata.closure_kind(def_id.index)
    }
    closure_ty in tcx.closure_tys -> ty::ClosureTy<'tcx> {
        cdata.closure_ty(def_id.index, tcx)
    }
}

impl CrateStore for cstore::CStore {
    fn describe_def(&self, def: DefId) -> Option<Def> {
        self.dep_graph.read(DepNode::MetaData(def));
        self.get_crate_data(def.krate).get_def(def.index)
    }

    fn stability(&self, def: DefId) -> Option<attr::Stability> {
        self.dep_graph.read(DepNode::MetaData(def));
        self.get_crate_data(def.krate).get_stability(def.index)
    }

    fn deprecation(&self, def: DefId) -> Option<attr::Deprecation> {
        self.dep_graph.read(DepNode::MetaData(def));
        self.get_crate_data(def.krate).get_deprecation(def.index)
    }

    fn visibility(&self, def: DefId) -> ty::Visibility {
        self.dep_graph.read(DepNode::MetaData(def));
        self.get_crate_data(def.krate).get_visibility(def.index)
    }

    fn item_attrs(&self, def_id: DefId) -> Vec<ast::Attribute>
    {
        self.dep_graph.read(DepNode::MetaData(def_id));
        self.get_crate_data(def_id.krate).get_item_attrs(def_id.index)
    }

    fn fn_arg_names(&self, did: DefId) -> Vec<ast::Name>
    {
        self.dep_graph.read(DepNode::MetaData(did));
        self.get_crate_data(did.krate).get_fn_arg_names(did.index)
    }

    fn inherent_implementations_for_type(&self, def_id: DefId) -> Vec<DefId>
    {
        self.dep_graph.read(DepNode::MetaData(def_id));
        self.get_crate_data(def_id.krate).get_inherent_implementations_for_type(def_id.index)
    }

    fn implementations_of_trait(&self, filter: Option<DefId>) -> Vec<DefId>
    {
        if let Some(def_id) = filter {
            self.dep_graph.read(DepNode::MetaData(def_id));
        }
        let mut result = vec![];
        self.iter_crate_data(|_, cdata| {
            cdata.get_implementations_for_trait(filter, &mut result)
        });
        result
    }

    fn impl_polarity(&self, def: DefId) -> hir::ImplPolarity
    {
        self.dep_graph.read(DepNode::MetaData(def));
        self.get_crate_data(def.krate).get_impl_polarity(def.index)
    }

    fn impl_parent(&self, impl_def: DefId) -> Option<DefId> {
        self.dep_graph.read(DepNode::MetaData(impl_def));
        self.get_crate_data(impl_def.krate).get_parent_impl(impl_def.index)
    }

    fn trait_of_item(&self, def_id: DefId) -> Option<DefId> {
        self.dep_graph.read(DepNode::MetaData(def_id));
        self.get_crate_data(def_id.krate).get_trait_of_item(def_id.index)
    }

    fn is_const_fn(&self, did: DefId) -> bool
    {
        self.dep_graph.read(DepNode::MetaData(did));
        self.get_crate_data(did.krate).is_const_fn(did.index)
    }

    fn is_defaulted_trait(&self, trait_def_id: DefId) -> bool
    {
        self.dep_graph.read(DepNode::MetaData(trait_def_id));
        self.get_crate_data(trait_def_id.krate).is_defaulted_trait(trait_def_id.index)
    }

    fn is_default_impl(&self, impl_did: DefId) -> bool {
        self.dep_graph.read(DepNode::MetaData(impl_did));
        self.get_crate_data(impl_did.krate).is_default_impl(impl_did.index)
    }

    fn is_foreign_item(&self, did: DefId) -> bool {
        self.get_crate_data(did.krate).is_foreign_item(did.index)
    }

    fn is_statically_included_foreign_item(&self, id: ast::NodeId) -> bool
    {
        self.do_is_statically_included_foreign_item(id)
    }

    fn dylib_dependency_formats(&self, cnum: CrateNum)
                                -> Vec<(CrateNum, LinkagePreference)>
    {
        self.get_crate_data(cnum).get_dylib_dependency_formats()
    }

    fn lang_items(&self, cnum: CrateNum) -> Vec<(DefIndex, usize)>
    {
        self.get_crate_data(cnum).get_lang_items()
    }

    fn missing_lang_items(&self, cnum: CrateNum)
                          -> Vec<lang_items::LangItem>
    {
        self.get_crate_data(cnum).get_missing_lang_items()
    }

    fn is_staged_api(&self, cnum: CrateNum) -> bool
    {
        self.get_crate_data(cnum).is_staged_api()
    }

    fn is_explicitly_linked(&self, cnum: CrateNum) -> bool
    {
        self.get_crate_data(cnum).explicitly_linked.get()
    }

    fn is_allocator(&self, cnum: CrateNum) -> bool
    {
        self.get_crate_data(cnum).is_allocator()
    }

    fn is_panic_runtime(&self, cnum: CrateNum) -> bool
    {
        self.get_crate_data(cnum).is_panic_runtime()
    }

    fn is_compiler_builtins(&self, cnum: CrateNum) -> bool {
        self.get_crate_data(cnum).is_compiler_builtins()
    }

    fn panic_strategy(&self, cnum: CrateNum) -> PanicStrategy {
        self.get_crate_data(cnum).panic_strategy()
    }

    fn crate_name(&self, cnum: CrateNum) -> token::InternedString
    {
        token::intern_and_get_ident(&self.get_crate_data(cnum).name[..])
    }

    fn original_crate_name(&self, cnum: CrateNum) -> token::InternedString
    {
        token::intern_and_get_ident(&self.get_crate_data(cnum).name())
    }

    fn extern_crate(&self, cnum: CrateNum) -> Option<ExternCrate>
    {
        self.get_crate_data(cnum).extern_crate.get()
    }

    fn crate_hash(&self, cnum: CrateNum) -> Svh
    {
        self.get_crate_hash(cnum)
    }

    fn crate_disambiguator(&self, cnum: CrateNum) -> token::InternedString
    {
        token::intern_and_get_ident(&self.get_crate_data(cnum).disambiguator())
    }

    fn plugin_registrar_fn(&self, cnum: CrateNum) -> Option<DefId>
    {
        self.get_crate_data(cnum).root.plugin_registrar_fn.map(|index| DefId {
            krate: cnum,
            index: index
        })
    }

    fn native_libraries(&self, cnum: CrateNum) -> Vec<(NativeLibraryKind, String)>
    {
        self.get_crate_data(cnum).get_native_libraries()
    }

    fn reachable_ids(&self, cnum: CrateNum) -> Vec<DefId>
    {
        self.get_crate_data(cnum).get_reachable_ids()
    }

    fn is_no_builtins(&self, cnum: CrateNum) -> bool {
        self.get_crate_data(cnum).is_no_builtins()
    }

    fn def_index_for_def_key(&self,
                             cnum: CrateNum,
                             def: DefKey)
                             -> Option<DefIndex> {
        let cdata = self.get_crate_data(cnum);
        cdata.key_map.get(&def).cloned()
    }

    /// Returns the `DefKey` for a given `DefId`. This indicates the
    /// parent `DefId` as well as some idea of what kind of data the
    /// `DefId` refers to.
    fn def_key(&self, def: DefId) -> hir_map::DefKey {
        // Note: loading the def-key (or def-path) for a def-id is not
        // a *read* of its metadata. This is because the def-id is
        // really just an interned shorthand for a def-path, which is the
        // canonical name for an item.
        //
        // self.dep_graph.read(DepNode::MetaData(def));
        self.get_crate_data(def.krate).def_key(def.index)
    }

    fn relative_def_path(&self, def: DefId) -> Option<hir_map::DefPath> {
        // See `Note` above in `def_key()` for why this read is
        // commented out:
        //
        // self.dep_graph.read(DepNode::MetaData(def));
        self.get_crate_data(def.krate).def_path(def.index)
    }

    fn struct_field_names(&self, def: DefId) -> Vec<ast::Name>
    {
        self.dep_graph.read(DepNode::MetaData(def));
        self.get_crate_data(def.krate).get_struct_field_names(def.index)
    }

    fn item_children(&self, def_id: DefId) -> Vec<def::Export>
    {
        self.dep_graph.read(DepNode::MetaData(def_id));
        let mut result = vec![];
        self.get_crate_data(def_id.krate)
            .each_child_of_item(def_id.index, |child| result.push(child));
        result
    }

    fn maybe_get_item_ast<'a, 'tcx>(&self,
                                    tcx: TyCtxt<'a, 'tcx, 'tcx>,
                                    def_id: DefId)
                                    -> Option<(&'tcx InlinedItem, ast::NodeId)>
    {
        self.dep_graph.read(DepNode::MetaData(def_id));

        match self.inlined_item_cache.borrow().get(&def_id) {
            Some(&None) => {
                return None; // Not inlinable
            }
            Some(&Some(ref cached_inlined_item)) => {
                // Already inline
                debug!("maybe_get_item_ast({}): already inline as node id {}",
                          tcx.item_path_str(def_id), cached_inlined_item.item_id);
                return Some((tcx.map.expect_inlined_item(cached_inlined_item.inlined_root),
                             cached_inlined_item.item_id));
            }
            None => {
                // Not seen yet
            }
        }

        debug!("maybe_get_item_ast({}): inlining item", tcx.item_path_str(def_id));

        let inlined = self.get_crate_data(def_id.krate).maybe_get_item_ast(tcx, def_id.index);

        let cache_inlined_item = |original_def_id, inlined_item_id, inlined_root_node_id| {
            let cache_entry = cstore::CachedInlinedItem {
                inlined_root: inlined_root_node_id,
                item_id: inlined_item_id,
            };
            self.inlined_item_cache
                .borrow_mut()
                .insert(original_def_id, Some(cache_entry));
            self.defid_for_inlined_node
                .borrow_mut()
                .insert(inlined_item_id, original_def_id);
        };

        let find_inlined_item_root = |inlined_item_id| {
            let mut node = inlined_item_id;
            let mut path = Vec::with_capacity(10);

            // If we can't find the inline root after a thousand hops, we can
            // be pretty sure there's something wrong with the HIR map.
            for _ in 0 .. 1000 {
                path.push(node);
                let parent_node = tcx.map.get_parent_node(node);
                if parent_node == node {
                    return node;
                }
                node = parent_node;
            }
            bug!("cycle in HIR map parent chain")
        };

        match inlined {
            None => {
                self.inlined_item_cache
                    .borrow_mut()
                    .insert(def_id, None);
            }
            Some(&InlinedItem::Item(d, ref item)) => {
                assert_eq!(d, def_id);
                let inlined_root_node_id = find_inlined_item_root(item.id);
                cache_inlined_item(def_id, item.id, inlined_root_node_id);
            }
            Some(&InlinedItem::TraitItem(_, ref trait_item)) => {
                let inlined_root_node_id = find_inlined_item_root(trait_item.id);
                cache_inlined_item(def_id, trait_item.id, inlined_root_node_id);

                // Associated consts already have to be evaluated in `typeck`, so
                // the logic to do that already exists in `middle`. In order to
                // reuse that code, it needs to be able to look up the traits for
                // inlined items.
                let ty_trait_item = tcx.associated_item(def_id).clone();
                let trait_item_def_id = tcx.map.local_def_id(trait_item.id);
                tcx.associated_items.borrow_mut()
                   .insert(trait_item_def_id, ty_trait_item);
            }
            Some(&InlinedItem::ImplItem(_, ref impl_item)) => {
                let inlined_root_node_id = find_inlined_item_root(impl_item.id);
                cache_inlined_item(def_id, impl_item.id, inlined_root_node_id);
            }
        }

        // We can be sure to hit the cache now
        return self.maybe_get_item_ast(tcx, def_id);
    }

    fn local_node_for_inlined_defid(&self, def_id: DefId) -> Option<ast::NodeId> {
        assert!(!def_id.is_local());
        match self.inlined_item_cache.borrow().get(&def_id) {
            Some(&Some(ref cached_inlined_item)) => {
                Some(cached_inlined_item.item_id)
            }
            Some(&None) => {
                None
            }
            _ => {
                bug!("Trying to lookup inlined NodeId for unexpected item");
            }
        }
    }

    fn defid_for_inlined_node(&self, node_id: ast::NodeId) -> Option<DefId> {
        self.defid_for_inlined_node.borrow().get(&node_id).map(|x| *x)
    }

    fn is_item_mir_available(&self, def: DefId) -> bool {
        self.dep_graph.read(DepNode::MetaData(def));
        self.get_crate_data(def.krate).is_item_mir_available(def.index)
    }

    fn crates(&self) -> Vec<CrateNum>
    {
        let mut result = vec![];
        self.iter_crate_data(|cnum, _| result.push(cnum));
        result
    }

    fn used_libraries(&self) -> Vec<(String, NativeLibraryKind)>
    {
        self.get_used_libraries().borrow().clone()
    }

    fn used_link_args(&self) -> Vec<String>
    {
        self.get_used_link_args().borrow().clone()
    }

    fn metadata_filename(&self) -> &str
    {
        locator::METADATA_FILENAME
    }

    fn metadata_section_name(&self, target: &Target) -> &str
    {
        locator::meta_section_name(target)
    }

    fn used_crates(&self, prefer: LinkagePreference) -> Vec<(CrateNum, Option<PathBuf>)>
    {
        self.do_get_used_crates(prefer)
    }

    fn used_crate_source(&self, cnum: CrateNum) -> CrateSource
    {
        self.opt_used_crate_source(cnum).unwrap()
    }

    fn extern_mod_stmt_cnum(&self, emod_id: ast::NodeId) -> Option<CrateNum>
    {
        self.do_extern_mod_stmt_cnum(emod_id)
    }

    fn encode_metadata<'a, 'tcx>(&self, tcx: TyCtxt<'a, 'tcx, 'tcx>,
                                 reexports: &def::ExportMap,
                                 link_meta: &LinkMeta,
                                 reachable: &NodeSet) -> Vec<u8>
    {
        encoder::encode_metadata(tcx, self, reexports, link_meta, reachable)
    }

    fn metadata_encoding_version(&self) -> &[u8]
    {
        schema::METADATA_HEADER
    }

    /// Returns a map from a sufficiently visible external item (i.e. an external item that is
    /// visible from at least one local module) to a sufficiently visible parent (considering
    /// modules that re-export the external item to be parents).
    fn visible_parent_map<'a>(&'a self) -> ::std::cell::RefMut<'a, DefIdMap<DefId>> {
        let mut visible_parent_map = self.visible_parent_map.borrow_mut();
        if !visible_parent_map.is_empty() { return visible_parent_map; }

        use std::collections::vec_deque::VecDeque;
        use std::collections::hash_map::Entry;
        for cnum in (1 .. self.next_crate_num().as_usize()).map(CrateNum::new) {
            let cdata = self.get_crate_data(cnum);

            match cdata.extern_crate.get() {
                // Ignore crates without a corresponding local `extern crate` item.
                Some(extern_crate) if !extern_crate.direct => continue,
                _ => {},
            }

            let mut bfs_queue = &mut VecDeque::new();
            let mut add_child = |bfs_queue: &mut VecDeque<_>, child: def::Export, parent: DefId| {
                let child = child.def.def_id();

                if self.visibility(child) != ty::Visibility::Public {
                    return;
                }

                match visible_parent_map.entry(child) {
                    Entry::Occupied(mut entry) => {
                        // If `child` is defined in crate `cnum`, ensure
                        // that it is mapped to a parent in `cnum`.
                        if child.krate == cnum && entry.get().krate != cnum {
                            entry.insert(parent);
                        }
                    }
                    Entry::Vacant(entry) => {
                        entry.insert(parent);
                        bfs_queue.push_back(child);
                    }
                }
            };

            bfs_queue.push_back(DefId {
                krate: cnum,
                index: CRATE_DEF_INDEX
            });
            while let Some(def) = bfs_queue.pop_front() {
                for child in self.item_children(def) {
                    add_child(bfs_queue, child, def);
                }
            }
        }

        visible_parent_map
    }
}
