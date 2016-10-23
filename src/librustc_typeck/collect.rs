// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*

# Collect phase

The collect phase of type check has the job of visiting all items,
determining their type, and writing that type into the `tcx.types`
table.  Despite its name, this table does not really operate as a
*cache*, at least not for the types of items defined within the
current crate: we assume that after the collect phase, the types of
all local items will be present in the table.

Unlike most of the types that are present in Rust, the types computed
for each item are in fact type schemes. This means that they are
generic types that may have type parameters. TypeSchemes are
represented by a pair of `Generics` and `Ty`.  Type
parameters themselves are represented as `ty_param()` instances.

The phasing of type conversion is somewhat complicated. There is no
clear set of phases we can enforce (e.g., converting traits first,
then types, or something like that) because the user can introduce
arbitrary interdependencies. So instead we generally convert things
lazilly and on demand, and include logic that checks for cycles.
Demand is driven by calls to `AstConv::get_item_type_scheme` or
`AstConv::lookup_trait_def`.

Currently, we "convert" types and traits in two phases (note that
conversion only affects the types of items / enum variants / methods;
it does not e.g. compute the types of individual expressions):

0. Intrinsics
1. Trait/Type definitions

Conversion itself is done by simply walking each of the items in turn
and invoking an appropriate function (e.g., `trait_def_of_item` or
`convert_item`). However, it is possible that while converting an
item, we may need to compute the *type scheme* or *trait definition*
for other items.

There are some shortcomings in this design:

- Because the item generics include defaults, cycles through type
  parameter defaults are illegal even if those defaults are never
  employed. This is not necessarily a bug.

*/

use rustc::dep_graph::DepNode;
use rustc::ty::TyCtxt;
use util::nodemap::FnvHashMap;

use std::collections::hash_map::Entry::{Occupied, Vacant};

use rustc::hir::{self, intravisit};

///////////////////////////////////////////////////////////////////////////
// Main entry point

pub fn collect_item_types<'a, 'tcx>(tcx: TyCtxt<'a, 'tcx, 'tcx>) {
    let mut visitor = CollectItemTypesVisitor { tcx: tcx };
    tcx.visit_all_items_in_krate(DepNode::CollectItem, &mut visitor);
}

struct CollectItemTypesVisitor<'a, 'tcx: 'a> {
    tcx: TyCtxt<'a, 'tcx, 'tcx>
}

impl<'a, 'tcx, 'v> intravisit::Visitor<'v> for CollectItemTypesVisitor<'a, 'tcx> {
    fn visit_item(&mut self, item: &hir::Item) {
        convert_item(self.tcx, item);
    }
}

fn convert_item<'a, 'tcx>(tcx: TyCtxt<'a, 'tcx, 'tcx>, it: &hir::Item) {
    debug!("convert: item {} with id {}", it.name, it.id);
    let def_id = tcx.map.local_def_id(it.id);
    match it.node {
        // These don't define types.
        hir::ItemExternCrate(_) | hir::ItemUse(_) | hir::ItemMod(_) => {
        }
        hir::ItemForeignMod(ref foreign_mod) => {
            for item in &foreign_mod.items {
                let def_id = tcx.map.local_def_id(item.id);
                tcx.item_generics(def_id);
                tcx.item_predicates(def_id);
                tcx.item_type(def_id);
            }
        }
        hir::ItemEnum(..) => {
            tcx.item_generics(def_id);
            tcx.item_predicates(def_id);
            tcx.item_type(def_id);
            let def = tcx.lookup_adt_def(tcx.map.local_def_id(it.id));
            for variant in &def.variants {
                for f in &variant.fields {
                    tcx.item_type(f.did);
                }
                tcx.item_generics(variant.did);
                tcx.item_predicates(variant.did);
                tcx.item_type(variant.did);
            }
        },
        hir::ItemDefaultImpl(..) => {
            if let Some(trait_ref) = tcx.impl_trait_ref(def_id) {
                tcx.record_trait_has_default_impl(trait_ref.def_id);
            }
        }
        hir::ItemImpl(.., ref impl_items) => {
            // Create generics from the generics specified in the impl head.
            tcx.item_generics(def_id);
            tcx.item_predicates(def_id);

            tcx.item_type(def_id);
            tcx.impl_trait_ref(def_id);

            // Convert all the associated consts.
            // Also, check if there are any duplicate associated items
            let mut seen_type_items = FnvHashMap();
            let mut seen_value_items = FnvHashMap();

            for impl_item in impl_items {
                let seen_items = match impl_item.node {
                    hir::ImplItemKind::Type(_) => &mut seen_type_items,
                    _                    => &mut seen_value_items,
                };
                match seen_items.entry(impl_item.name) {
                    Occupied(entry) => {
                        let mut err = struct_span_err!(tcx.sess, impl_item.span, E0201,
                                                       "duplicate definitions with name `{}`:",
                                                       impl_item.name);
                        err.span_label(*entry.get(),
                                   &format!("previous definition of `{}` here",
                                        impl_item.name));
                        err.span_label(impl_item.span, &format!("duplicate definition"));
                        err.emit();
                    }
                    Vacant(entry) => {
                        entry.insert(impl_item.span);
                    }
                }
            }

            for impl_item in impl_items {
                let def_id = tcx.map.local_def_id(impl_item.id);
                tcx.item_generics(def_id);
                tcx.item_predicates(def_id);
                tcx.item_type(def_id);
            }
        },
        hir::ItemTrait(.., ref trait_items) => {
            tcx.lookup_trait_def(def_id);
            tcx.item_generics(def_id);
            tcx.item_predicates(def_id);

            for trait_item in trait_items {
                let def_id = tcx.map.local_def_id(trait_item.id);
                tcx.item_generics(def_id);
                tcx.item_predicates(def_id);

                // Skip the type if it doesn't exist
                if let hir::TypeTraitItem(_, ref opt_ty) = trait_item.node {
                    if opt_ty.is_none() {
                        continue;
                    }
                }

                tcx.item_type(def_id);
            }
        },
        hir::ItemStruct(ref struct_def, _) |
        hir::ItemUnion(ref struct_def, _) => {
            tcx.item_generics(def_id);
            tcx.item_predicates(def_id);
            tcx.item_type(def_id);

            let variant = tcx.lookup_adt_def(def_id).struct_variant();
            for f in &variant.fields {
                tcx.item_type(f.did);
            }

            if !struct_def.is_struct() {
                let def_id = tcx.map.local_def_id(struct_def.id());
                tcx.item_generics(def_id);
                tcx.item_predicates(def_id);
                tcx.item_type(def_id);
            }
        }
        _ => {
            tcx.item_generics(def_id);
            tcx.item_predicates(def_id);
            tcx.item_type(def_id);
        },
    }
}
