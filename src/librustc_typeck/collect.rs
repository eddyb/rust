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

use constrained_type_params as ctp;
use rustc::dep_graph::DepNode;
use rustc::ty::{self, TyCtxt};
use util::nodemap::{FnvHashMap, FnvHashSet};

use std::collections::hash_map::Entry::{Occupied, Vacant};

use syntax::abi;
use syntax_pos::Span;

use rustc::hir::{self, intravisit, print as pprust};
use rustc::hir::def_id::DefId;

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

fn ensure_no_ty_param_bounds(tcx: TyCtxt, span: Span, generics: &hir::Generics) {
    let warn = generics.ty_params.iter().flat_map(|p| &p.bounds).any(|bound| {
        match *bound {
            hir::TraitTyParamBound(..) => true,
            hir::RegionTyParamBound(..) => false
        }
    });

    if warn {
        // According to accepted RFC #XXX, we should
        // eventually accept these, but it will not be
        // part of this PR. Still, convert to warning to
        // make bootstrapping easier.
        span_warn!(tcx.sess, span, E0122,
                   "trait bounds are not (yet) enforced \
                    in type definitions");
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
                convert_foreign_item(tcx, item);
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
        hir::ItemImpl(.., ref generics, _, _, ref impl_items) => {
            // Create generics from the generics specified in the impl head.
            debug!("convert: ast_generics={:?}", generics);
            tcx.item_generics(def_id);
            let ty_predicates = tcx.item_predicates(def_id);

            debug!("convert: impl_bounds={:?}", ty_predicates);

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

            let mut ty_predicates = (*ty_predicates).clone();
            enforce_impl_params_are_constrained(tcx, generics, &mut ty_predicates, def_id);
            enforce_impl_lifetimes_are_constrained(tcx, generics, def_id, impl_items);
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
        },
        hir::ItemTy(_, ref generics) => {
            ensure_no_ty_param_bounds(tcx, it.span, generics);
            tcx.item_generics(def_id);
            tcx.item_predicates(def_id);
            tcx.item_type(def_id);
        },
        _ => {
            tcx.item_generics(def_id);
            tcx.item_predicates(def_id);
            tcx.item_type(def_id);
        },
    }
}

fn convert_foreign_item<'a, 'tcx>(tcx: TyCtxt<'a, 'tcx, 'tcx>,
                                  it: &hir::ForeignItem)
{
    let def_id = tcx.map.local_def_id(it.id);
    tcx.item_generics(def_id);
    tcx.item_predicates(def_id);
    let ty = tcx.item_type(def_id);

    let decl = match it.node {
        hir::ForeignItemFn(ref decl, _) => decl,
        _ => return
    };

    let abi = tcx.map.get_foreign_abi(it.id);

    // feature gate SIMD types in FFI, since I (huonw) am not sure the
    // ABIs are handled at all correctly.
    if abi != abi::Abi::RustIntrinsic && abi != abi::Abi::PlatformIntrinsic
            && !tcx.sess.features.borrow().simd_ffi {
        let check = |ast_ty: &hir::Ty, ty: ty::Ty| {
            if ty.is_simd() {
                tcx.sess.struct_span_err(ast_ty.span,
                              &format!("use of SIMD type `{}` in FFI is highly experimental and \
                                        may result in invalid code",
                                       pprust::ty_to_string(ast_ty)))
                    .help("add #![feature(simd_ffi)] to the crate attributes to enable")
                    .emit();
            }
        };
        let sig = ty.fn_sig();
        for (input, ty) in decl.inputs.iter().zip(sig.inputs().skip_binder()) {
            check(&input.ty, ty)
        }
        if let hir::Return(ref ty) = decl.output {
            check(&ty, sig.output().skip_binder())
        }
    }
}

/// Checks that all the type parameters on an impl
fn enforce_impl_params_are_constrained<'a, 'tcx>(tcx: TyCtxt<'a, 'tcx, 'tcx>,
                                                 generics: &hir::Generics,
                                                 impl_predicates: &mut ty::GenericPredicates<'tcx>,
                                                 impl_def_id: DefId)
{
    let impl_ty = tcx.item_type(impl_def_id);
    let impl_trait_ref = tcx.impl_trait_ref(impl_def_id);

    // The trait reference is an input, so find all type parameters
    // reachable from there, to start (if this is an inherent impl,
    // then just examine the self type).
    let mut input_parameters: FnvHashSet<_> =
        ctp::parameters_for(&impl_ty, false).into_iter().collect();
    if let Some(ref trait_ref) = impl_trait_ref {
        input_parameters.extend(ctp::parameters_for(trait_ref, false));
    }

    ctp::setup_constraining_predicates(&mut impl_predicates.predicates,
                                       impl_trait_ref,
                                       &mut input_parameters);

    let ty_generics = tcx.item_generics(impl_def_id);
    for (ty_param, param) in ty_generics.types.iter().zip(&generics.ty_params) {
        let param_ty = ty::ParamTy::for_def(ty_param);
        if !input_parameters.contains(&ctp::Parameter::from(param_ty)) {
            report_unused_parameter(tcx, param.span, "type", &param_ty.to_string());
        }
    }
}

fn enforce_impl_lifetimes_are_constrained<'a, 'tcx>(tcx: TyCtxt<'a, 'tcx, 'tcx>,
                                                    ast_generics: &hir::Generics,
                                                    impl_def_id: DefId,
                                                    impl_items: &[hir::ImplItem])
{
    // Every lifetime used in an associated type must be constrained.
    let impl_ty = tcx.item_type(impl_def_id);
    let impl_predicates = tcx.item_predicates(impl_def_id);
    let impl_trait_ref = tcx.impl_trait_ref(impl_def_id);

    let mut input_parameters: FnvHashSet<_> =
        ctp::parameters_for(&impl_ty, false).into_iter().collect();
    if let Some(ref trait_ref) = impl_trait_ref {
        input_parameters.extend(ctp::parameters_for(trait_ref, false));
    }
    ctp::identify_constrained_type_params(
        &impl_predicates.predicates.as_slice(), impl_trait_ref, &mut input_parameters);

    let lifetimes_in_associated_types: FnvHashSet<_> = impl_items.iter()
        .map(|item| tcx.map.local_def_id(item.id))
        .filter(|&def_id| {
            let item = tcx.associated_item(def_id);
            item.kind == ty::AssociatedKind::Type && item.has_value
        })
        .flat_map(|def_id| {
            ctp::parameters_for(&tcx.item_type(def_id), true)
        }).collect();

    for (ty_lifetime, lifetime) in tcx.item_generics(impl_def_id).regions.iter()
        .zip(&ast_generics.lifetimes)
    {
        let param = ctp::Parameter::from(ty_lifetime.to_early_bound_region_data());

        if
            lifetimes_in_associated_types.contains(&param) && // (*)
            !input_parameters.contains(&param)
        {
            report_unused_parameter(tcx, lifetime.lifetime.span,
                                    "lifetime", &lifetime.lifetime.name.to_string());
        }
    }

    // (*) This is a horrible concession to reality. I think it'd be
    // better to just ban unconstrianed lifetimes outright, but in
    // practice people do non-hygenic macros like:
    //
    // ```
    // macro_rules! __impl_slice_eq1 {
    //     ($Lhs: ty, $Rhs: ty, $Bound: ident) => {
    //         impl<'a, 'b, A: $Bound, B> PartialEq<$Rhs> for $Lhs where A: PartialEq<B> {
    //            ....
    //         }
    //     }
    // }
    // ```
    //
    // In a concession to backwards compatbility, we continue to
    // permit those, so long as the lifetimes aren't used in
    // associated types. I believe this is sound, because lifetimes
    // used elsewhere are not projected back out.
}

fn report_unused_parameter(tcx: TyCtxt, span: Span, kind: &str, name: &str) {
    struct_span_err!(
        tcx.sess, span, E0207,
        "the {} parameter `{}` is not constrained by the \
        impl trait, self type, or predicates",
        kind, name)
        .span_label(span, &format!("unconstrained {} parameter", kind))
        .emit();
}
