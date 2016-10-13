// Copyright 2016 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use astconv::{AstConv, ast_region_to_region, SizedByDefault};
use rscope::*;

use rustc::hir;
use rustc::hir::def::Def;
use rustc::hir::def_id::DefId;
use rustc::hir::intravisit::{self, Visitor};
use rustc::lint;
use rustc::ty::{self, ToPolyTraitRef, Ty, TyCtxt, ToPredicate, TypeFoldable};
use rustc::ty::demand::{Provider, Unsupported};
use rustc::ty::fold::TypeVisitor;
use rustc::ty::subst::Substs;
use rustc::ty::util::IntTypeExt;
use rustc::util::common::MemoizationMap;
use rustc::util::nodemap::{NodeMap, FnvHashMap, FnvHashSet};

use rustc::middle::const_val::ConstVal;
use rustc::middle::resolve_lifetime as rl;
use rustc_const_eval::EvalHint::UncheckedExprHint;
use rustc_const_eval::{eval_const_expr_partial, report_const_eval_err};
use rustc_const_math::ConstInt;
use rustc_data_structures::bitvec::BitVector;

use syntax::{abi, ast, attr};
use syntax::codemap::Spanned;
use syntax::parse::token::keywords;
use syntax_pos::Span;

use std::cell::{Cell, RefCell};
use std::collections::hash_map::Entry;
use std::iter;
use std::rc::Rc;

#[derive(Default)]
pub struct TypeckProvider<'tcx> {
    /// Cache for `AstConv::ast_ty_to_ty`. Also serves
    /// to catch reentrance and produce `TyIncomplete`.
    ty_cache: RefCell<NodeMap<TyCacheEntry<'tcx>>>,

    /// Stack of requests made to `TypeckProvider`.
    /// Used to catch and report some cycles.
    stack: RefCell<RequestStack>,

    /// Information for each generated `TyIncomplete`,
    /// used to report cycles in case they leak into
    /// the final result of some request.
    incomplete_types: RefCell<NodeMap<IncompleteInfo<'tcx>>>,

    /// IDs for `TyIncomplete`, grouped by the containing
    /// request, so we can reclaim memory for those that
    /// didn't end up in some result and won't be reported.
    pending_incomplete: RefCell<FnvHashMap<(Request, ast::NodeId),
                                           Vec<ast::NodeId>>>
}

#[derive(Copy, Clone)]
enum TyCacheEntry<'tcx> {
    Done(Ty<'tcx>),
    Incomplete
}

struct IncompleteInfo<'tcx> {
    /// Cached `TyIncomplete`.
    ty: Ty<'tcx>,

    /// The deepest cycle in the request stack,
    /// at the point where the `TyIncomplete`
    /// was first created for this type node.
    cycle: RequestStack
}

type RequestStack = Vec<(Request, ast::NodeId)>;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
enum Request {
    /// Should never recurse - if it does, just ICE.
    Leaf,

    AdtDef,
    Generics,
    SuperPredicates,
    Predicates,
    Type,
    ImplTraitRef
}

impl Request {
    fn describe(&self) -> &str {
        match *self {
            Request::SuperPredicates => "computing the supertraits of",
            Request::Predicates => "computing the bounds of",
            _ => "processing"
        }
    }
}

fn report_cycle(tcx: TyCtxt,
                span: Span,
                cycle: &[(Request, ast::NodeId)]) {
    let mut err = struct_span_err!(tcx.sess, span, E0391,
        "unsupported cyclic reference between types/traits detected");
    err.span_label(span, &format!("cyclic reference"));

    let (request, id) = cycle[0];
    err.note(&format!("the cycle begins when {} `{}`...",
                      request.describe(),
                      tcx.item_path_str(tcx.map.local_def_id(id))));

    for &(request, id) in &cycle[1..] {
        err.note(&format!("...which then requires {} `{}`...",
                          request.describe(),
                          tcx.item_path_str(tcx.map.local_def_id(id))));
    }

    err.note(&format!("...which then again requires {} `{}`, completing the cycle.",
                      request.describe(),
                      tcx.item_path_str(tcx.map.local_def_id(id))));

    err.emit();
}

impl<'tcx> TypeckProvider<'tcx> {
    /// Checks for a cycle through the same request/node pair,
    /// and returns `false` in case a cycle error was found.
    fn cycle_check(&self, tcx: TyCtxt, request: Request, id: ast::NodeId) -> bool {
        let mut stack = self.stack.borrow_mut();
        match stack.iter().enumerate().rev().find(|&(_, r)| *r == (request, id)) {
            None => { }
            Some((i, _)) => {
                report_cycle(tcx, tcx.map.span(id), &stack[i..]);
                return false;
            }
        }
        stack.push((request, id));
        true
    }
}

struct ItemCtxt<'a, 'tcx: 'a> {
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    provider: &'a TypeckProvider<'tcx>,
    def_id: DefId,
    last_incomplete: Cell<Option<ast::NodeId>>
}

struct ReportIncompleteAsCycle<'a, 'tcx: 'a> {
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    incomplete_types: &'a mut NodeMap<IncompleteInfo<'tcx>>
}

impl<'a, 'tcx> TypeVisitor<'tcx> for ReportIncompleteAsCycle<'a, 'tcx> {
    fn visit_ty(&mut self, ty: Ty<'tcx>) -> bool {
        if let ty::TyIncomplete(id, _) = ty.sty {
            // Avoid reporting the same type twice.
            if let Some(incomplete) = self.incomplete_types.remove(&id) {
                let span = self.tcx.map.span(id);
                report_cycle(self.tcx, span, &incomplete.cycle);
            }
        }

        ty.super_visit_with(self)
    }
}

impl<'a, 'tcx> ItemCtxt<'a, 'tcx> {
    fn to_ty<RS:RegionScope>(&self, rs: &RS, ast_ty: &hir::Ty) -> Ty<'tcx> {
        AstConv::ast_ty_to_ty(self, rs, ast_ty)
    }

    /// Report any `TyIncomplete` that are left around, as cycles,
    /// and throw away the information for ones that were resolved,
    /// if this is the only instance of this request, otherwise
    /// clear the `TyCacheEntry::Incomplete` type cache entries
    /// in case the types can later be completed.
    /// Returns `true` if the result of the request can be cached.
    fn sanitize<'b, T: 'b, I>(self, values: I) -> bool
    where I: Iterator<Item=&'b T>,
          T: TypeFoldable<'tcx> {
        let mut pending_incomplete = self.provider.pending_incomplete.borrow_mut();
        let current = {
            let stack = self.provider.stack.borrow();
            let current = *stack.last().unwrap();
            if stack[..stack.len() - 1].contains(&current) {
                // Clear the type cache of all the incomplete entries.
                // FIXME(eddyb) Figure out how to do this without
                // resulting in infinite recursion in some edge
                // cases. Possibly only clear those that were
                // introduced in this stack frame, not just this
                // specific request. Could do this by stack depth.
                /*if let Some(ids) = pending_incomplete.get(&current) {
                    let mut cache = self.provider.ty_cache.borrow_mut();
                    for &id in ids {
                        if let Entry::Occupied(entry) = cache.entry(id) {
                            if let TyCacheEntry::Incomplete = *entry.get() {
                                entry.remove();
                            }
                        }
                    }
                }*/

                // This is a nested request, can't cache it
                // without risking unnecessary failures.
                return false;
            }

            current
        };

        let mut incomplete_types = self.provider.incomplete_types.borrow_mut();
        {
            let mut reporter = ReportIncompleteAsCycle {
                tcx: self.tcx,
                incomplete_types: &mut incomplete_types
            };

            // Only visit the types if there's something to report on.
            for value in values {
                if value.references_incomplete() {
                    value.visit_with(&mut reporter);
                }
            }
        }

        // Destroy all the `TyIncomplete` information associated with this
        // request - the ones that don't show up would just waste memory,
        // and if they haven't surfaced already, in this request, or some
        // other one using a previous, less complete result, they can't.
        if let Some(ids) = pending_incomplete.remove(&current) {
            for id in ids {
                incomplete_types.remove(&id);
            }
        }

        true
    }
}

impl<'a, 'tcx> Drop for ItemCtxt<'a, 'tcx> {
    fn drop(&mut self) {
        assert!(self.provider.stack.borrow_mut().pop().is_some());
    }
}

struct ParamUseFinder<'a, 'tcx: 'a> {
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    num_types: usize,
    types: BitVector,
    num_regions: usize,
    regions: BitVector,
}

impl<'v, 'a, 'tcx> Visitor<'v> for ParamUseFinder<'a, 'tcx> {
    fn visit_ty(&mut self, ty: &hir::Ty) {
        let def = self.tcx.def_map.borrow().get(&ty.id).map(|r| r.base_def);
        if let Some(Def::TyParam(def_id)) = def {
            if let Some(node_id) = self.tcx.map.as_local_node_id(def_id) {
                if let Some(p) = self.tcx.ty_param_defs.borrow().get(&node_id) {
                    self.types.insert(p.index as usize);
                }
            }
        }

        // Every `impl Trait` captures all parameters in scope.
        if let hir::TyImplTrait(..) = ty.node {
            for i in 0..self.num_types {
                self.types.insert(i);
            }
            for i in 0..self.num_regions {
                self.regions.insert(i);
            }
        }

        intravisit::walk_ty(self, ty);
    }

    fn visit_lifetime(&mut self, lifetime: &hir::Lifetime) {
        let def = self.tcx.named_region_map.defs.get(&lifetime.id).cloned();
        if let Some(rl::DefEarlyBoundRegion(index, _)) = def {
            self.regions.insert(index as usize);
        }

        intravisit::walk_lifetime(self, lifetime);
    }
}

impl<'a, 'tcx> AstConv<'tcx, 'tcx> for ItemCtxt<'a, 'tcx> {
    fn tcx<'b>(&'b self) -> TyCtxt<'b, 'tcx, 'tcx> { self.tcx }

    fn ty_cache_lookup(&self, hir_ty: &hir::Ty) -> Option<Ty<'tcx>> {
        let id = hir_ty.id;
        let mut cache = self.provider.ty_cache.borrow_mut();
        match cache.get(&id).cloned() {
            Some(TyCacheEntry::Done(ty)) => return Some(ty),
            Some(TyCacheEntry::Incomplete) => {
                // Try to get a cached version of this `TyIncomplete`.
                if let Some(incomplete) = self.provider.incomplete_types.borrow().get(&id) {
                    return Some(incomplete.ty);
                }

                // Get the deepest request cycle stack.
                let (current, cycle) = {
                    let stack = self.provider.stack.borrow();
                    let current = *stack.last().unwrap();
                    let stack = &stack[..stack.len() - 1];
                    match stack.iter().enumerate().rev().find(|&(_, r)| *r == current) {
                        None => {
                            span_bug!(self.tcx.map.span(id),
                                      "item {:?} not found for cycle", self.def_id);
                        }
                        Some((i, _)) => (current, stack[i..].to_vec())
                    }
                };

                // The only way this type could be reached again
                // through generics is for defaults, and those
                // aren't used by substitutions, so we should
                // be able to have a dummy in there for that.
                cache.insert(id, TyCacheEntry::Done(self.tcx.types.err));

                // Take out the borrow for the duration of the call.
                drop(cache);
                let generics = self.tcx.item_generics(self.def_id);

                // Collect the type and lifetime parameters used
                // inside the type - we don't want to use parameters
                // that don't show up and trigger unrelated errors.
                let num_types = generics.parent_types as usize + generics.types.len();
                let num_regions = generics.parent_regions as usize + generics.regions.len();
                let mut param_uses = ParamUseFinder {
                    tcx: self.tcx,
                    num_types: num_types,
                    types: BitVector::new(num_types),
                    num_regions: num_regions,
                    regions: BitVector::new(num_regions),
                };
                param_uses.visit_ty(hir_ty);

                // Construct the identity substitutions, using 'static for
                // unused lifetime parameters and ! for unused type parameters.
                let substs = Substs::for_item(self.tcx, self.def_id, |def, _| {
                    if param_uses.regions.contains(def.index as usize) {
                        let early_bound = def.to_early_bound_region_data();
                        self.tcx.mk_region(ty::ReEarlyBound(early_bound))
                    } else {
                        self.tcx.mk_region(ty::ReStatic)
                    }
                }, |def, _| {
                    if param_uses.types.contains(def.index as usize) {
                        self.tcx.mk_param_from_def(def)
                    } else {
                        self.tcx.types.never
                    }
                });

                let ty = self.tcx.mk_ty(ty::TyIncomplete(id, substs));

                // Record that this item has a stack for this type.
                self.provider.pending_incomplete.borrow_mut()
                    .entry(current).or_insert(vec![]).push(id);

                // Cache the information associated with this type.
                self.provider.incomplete_types.borrow_mut().insert(id, IncompleteInfo {
                    ty: ty,
                    cycle: cycle
                });

                // Return the cache entry back to the "incomplete" state,
                // in which it will remain until the request finishes.
                self.provider.ty_cache.borrow_mut().insert(id, TyCacheEntry::Incomplete);

                return Some(ty);
            }
            None => {
                cache.insert(id, TyCacheEntry::Incomplete);
            }
        }

        // This is the deepest point in the recursion.
        // We don't want to create `TyIncomplete` for
        // any ancestor, if we can avoid it, so we'll
        // try to exonorate ancestors as we go down.

        // `last_incomplete`, if present, will either
        // be the immediate parent (the only other
        // `Incomplete` cache entry), or a descendant
        // of a sibling, which is already complete.
        if let Some(last) = self.last_incomplete.get() {
            if let Entry::Occupied(entry) = cache.entry(last) {
                if let TyCacheEntry::Incomplete = *entry.get() {
                    entry.remove();
                }
            }
        }

        // Now this is the only type in this request
        // that can become a `TyIncomplete`, let the
        // next know whom to exonorate in its turn.
        self.last_incomplete.set(Some(id));

        None
    }

    fn ty_cache_insert(&self, hir_ty: &hir::Ty, ty: Ty<'tcx>) {
        // Don't cache incomplete types.
        if !ty.references_incomplete() {
            self.provider.ty_cache.borrow_mut().insert(hir_ty.id, TyCacheEntry::Done(ty));
        }
    }

    fn get_free_substs(&self) -> Option<&Substs<'tcx>> {
        None
    }

    fn get_type_bounds(&self, ty: Ty<'tcx>) -> Vec<ty::PolyTraitRef<'tcx>> {
        // Traverse the parents to find all applying predicates.
        let mut result = vec![];
        let mut def_id = self.def_id;
        loop {
            let predicates = self.tcx.item_predicates(def_id);
            result.extend(predicates.predicates.iter().filter_map(|predicate| {
                match *predicate {
                    ty::Predicate::Trait(ref data) => {
                        if data.0.self_ty() == ty {
                            Some(data.to_poly_trait_ref())
                        } else {
                            None
                        }
                    }
                    _ => None
                }
            }));

            if let Some(parent) = predicates.parent {
                def_id = parent;
            } else {
                return result;
            }
        }
    }

    fn ty_infer(&self, span: Span) -> Ty<'tcx> {
        struct_span_err!(
            self.tcx.sess,
            span,
            E0121,
            "the type placeholder `_` is not allowed within types on item signatures"
        ).span_label(span, &format!("not allowed in type signatures"))
        .emit();
        self.tcx.types.err
    }

    fn projected_ty_from_poly_trait_ref(&self,
                                        span: Span,
                                        poly_trait_ref: ty::PolyTraitRef<'tcx>,
                                        item_name: ast::Name)
                                        -> Ty<'tcx>
    {
        if let Some(trait_ref) = self.tcx.no_late_bound_regions(&poly_trait_ref) {
            self.projected_ty(span, trait_ref, item_name)
        } else {
            // no late-bound regions, we can just ignore the binder
            span_err!(self.tcx.sess, span, E0212,
                "cannot extract an associated type from a higher-ranked trait bound \
                 in this context");
            self.tcx.types.err
        }
    }

    fn projected_ty(&self,
                    _span: Span,
                    trait_ref: ty::TraitRef<'tcx>,
                    item_name: ast::Name)
                    -> Ty<'tcx>
    {
        self.tcx.mk_projection(trait_ref, item_name)
    }

    fn set_tainted_by_errors(&self) {
        // no obvious place to track this, just let it go
    }
}

/// Tests whether this is the AST for a reference to the type
/// parameter with id `param_id`. We use this so as to avoid running
/// `ast_ty_to_ty`, because we want to avoid triggering an all-out
/// conversion of the type to avoid inducing unnecessary cycles.
fn is_param(tcx: TyCtxt, ast_ty: &hir::Ty, param_id: ast::NodeId) -> bool {
    if let hir::TyPath(None, _) = ast_ty.node {
        let path_res = tcx.expect_resolution(ast_ty.id);
        match path_res.base_def {
            Def::SelfTy(Some(def_id), None) |
            Def::TyParam(def_id) if path_res.depth == 0 => {
                def_id == tcx.map.local_def_id(param_id)
            }
            _ => false
        }
    } else {
        false
    }
}

/// Scan the bounds and where-clauses on a parameter to extract bounds
/// of the form `T:'a` so as to determine the `ObjectLifetimeDefault`.
/// This runs as part of computing the minimal type scheme, so we
/// intentionally avoid just asking astconv to convert all the where
/// clauses into a `ty::Predicate`. This is because that could induce
/// artificial cycles.
fn compute_object_lifetime_default<'a, 'tcx>(tcx: TyCtxt<'a, 'tcx, 'tcx>,
                                             param_id: ast::NodeId,
                                             param_bounds: &[hir::TyParamBound],
                                             where_clause: &hir::WhereClause)
                                             -> ty::ObjectLifetimeDefault<'tcx>
{
    fn from_bounds<'a, 'tcx>(tcx: TyCtxt<'a, 'tcx, 'tcx>,
                             bounds: &'a [hir::TyParamBound])
                             -> impl Iterator<Item = &'tcx ty::Region> + 'a {
        bounds.iter().filter_map(move |bound| {
            match *bound {
                hir::TraitTyParamBound(..) => None,
                hir::RegionTyParamBound(ref lifetime) => {
                    Some(ast_region_to_region(tcx, lifetime))
                }
            }
        })
    }

    fn from_predicates<'a, 'tcx>(tcx: TyCtxt<'a, 'tcx, 'tcx>,
                                 param_id: ast::NodeId,
                                 predicates: &'a [hir::WherePredicate])
                                 -> impl Iterator<Item = &'tcx ty::Region> + 'a {
        predicates.iter().flat_map(move |predicate| {
            let bounds = match *predicate {
                hir::WherePredicate::BoundPredicate(ref data) => {
                    if data.bound_lifetimes.is_empty() &&
                       is_param(tcx, &data.bounded_ty, param_id) {
                        &data.bounds
                    } else {
                        &[][..]
                    }
                }
                hir::WherePredicate::RegionPredicate(..) |
                hir::WherePredicate::EqPredicate(..) => &[]
            };
            from_bounds(tcx, bounds)
        })
    }

    let inline_bounds = from_bounds(tcx, param_bounds);
    let where_bounds = from_predicates(tcx, param_id, &where_clause.predicates);
    let all_bounds: FnvHashSet<_> = inline_bounds.chain(where_bounds).collect();
    if all_bounds.len() > 1 {
        ty::ObjectLifetimeDefault::Ambiguous
    } else if all_bounds.len() == 0 {
        ty::ObjectLifetimeDefault::BaseDefault
    } else {
        ty::ObjectLifetimeDefault::Specific(
            all_bounds.into_iter().next().unwrap())
    }
}

/// Converts a specific TyParamBound from the AST into a set of
/// predicates that apply to the self-type. A vector is returned
/// because this can be anywhere from 0 predicates (`T:?Sized` adds no
/// predicates) to 1 (`T:Foo`) to many (`T:Bar<X=i32>` adds `T:Bar`
/// and `<T as Bar>::X == i32`).
fn predicates_from_bound<'tcx>(astconv: &AstConv<'tcx, 'tcx>,
                               param_ty: Ty<'tcx>,
                               bound: &hir::TyParamBound)
                               -> Vec<ty::Predicate<'tcx>>
{
    match *bound {
        hir::TraitTyParamBound(ref tr, hir::TraitBoundModifier::None) => {
            let mut projections = Vec::new();
            let pred = astconv.instantiate_poly_trait_ref(&ExplicitRscope,
                                                          tr,
                                                          param_ty,
                                                          &mut projections);
            projections.into_iter()
                       .map(|p| p.to_predicate())
                       .chain(Some(pred.to_predicate()))
                       .collect()
        }
        hir::RegionTyParamBound(ref lifetime) => {
            let region = ast_region_to_region(astconv.tcx(), lifetime);
            let pred = ty::Binder(ty::OutlivesPredicate(param_ty, region));
            vec![ty::Predicate::TypeOutlives(pred)]
        }
        hir::TraitTyParamBound(_, hir::TraitBoundModifier::Maybe) => {
            Vec::new()
        }
    }
}

fn convert_variant<'a, 'tcx>(tcx: TyCtxt<'a, 'tcx, 'tcx>,
                             def_id: DefId,
                             name: ast::Name,
                             discr_val: ty::Disr,
                             def: &hir::VariantData)
                             -> ty::VariantDef {
    let mut seen_fields: FnvHashMap<ast::Name, Span> = FnvHashMap();
    let node_id = tcx.map.as_local_node_id(def_id).unwrap();
    let fields = def.fields().iter().map(|f| {
        let fid = tcx.map.local_def_id(f.id);
        let dup_span = seen_fields.get(&f.name).cloned();
        if let Some(prev_span) = dup_span {
            struct_span_err!(tcx.sess, f.span, E0124,
                             "field `{}` is already declared",
                             f.name)
                .span_label(f.span, &"field already declared")
                .span_label(prev_span, &format!("`{}` first declared here", f.name))
                .emit();
        } else {
            seen_fields.insert(f.name, f.span);
        }

        ty::FieldDef {
            did: fid,
            name: f.name,
            vis: ty::Visibility::from_hir(&f.vis, node_id, tcx)
        }
    }).collect();
    ty::VariantDef {
        did: def_id,
        name: name,
        disr_val: discr_val,
        fields: fields,
        ctor_kind: hir::def::CtorKind::from_hir(def),
    }
}

fn evaluate_discr_expr<'a, 'tcx>(tcx: TyCtxt<'a, 'tcx, 'tcx>,
                                 repr_ty: attr::IntType,
                                 e: &hir::Expr)
                                 -> Option<ty::Disr> {
    debug!("discr expr, checking {}", hir::print::expr_to_string(e));

    let ty_hint = repr_ty.to_ty(tcx);
    let print_err = |cv: ConstVal| {
        struct_span_err!(tcx.sess, e.span, E0079, "mismatched types")
            .note_expected_found(&"type", &ty_hint, &format!("{}", cv.description()))
            .span_label(e.span, &format!("expected '{}' type", ty_hint))
            .emit();
    };

    let hint = UncheckedExprHint(ty_hint);
    match eval_const_expr_partial(tcx, e, hint, None) {
        Ok(ConstVal::Integral(i)) => {
            // FIXME: eval_const_expr_partial should return an error if the hint is wrong
            match (repr_ty, i) {
                (attr::SignedInt(ast::IntTy::I8), ConstInt::I8(_)) |
                (attr::SignedInt(ast::IntTy::I16), ConstInt::I16(_)) |
                (attr::SignedInt(ast::IntTy::I32), ConstInt::I32(_)) |
                (attr::SignedInt(ast::IntTy::I64), ConstInt::I64(_)) |
                (attr::SignedInt(ast::IntTy::Is), ConstInt::Isize(_)) |
                (attr::UnsignedInt(ast::UintTy::U8), ConstInt::U8(_)) |
                (attr::UnsignedInt(ast::UintTy::U16), ConstInt::U16(_)) |
                (attr::UnsignedInt(ast::UintTy::U32), ConstInt::U32(_)) |
                (attr::UnsignedInt(ast::UintTy::U64), ConstInt::U64(_)) |
                (attr::UnsignedInt(ast::UintTy::Us), ConstInt::Usize(_)) => Some(i),
                (_, i) => {
                    print_err(ConstVal::Integral(i));
                    None
                },
            }
        },
        Ok(cv) => {
            print_err(cv);
            None
        },
        // enum variant evaluation happens before the global constant check
        // so we need to report the real error
        Err(err) => {
            let mut diag = report_const_eval_err(tcx, &err, e.span, "enum discriminant");
            diag.emit();
            None
        }
    }
}

/// Enter an `ItemCtxt` for a specific `DefId` and `Request`.
/// This returns `Unsupported` for non-local `DefId`s and checks
/// for cycles - which can be ignored with `ignore` or handled
/// with `Foo => fallback_expression` where `Foo` is a `Request`
/// variant (e.g. `Type => return Ok(tcx.types.err)`).
macro_rules! enter {
    ($this:ident, $tcx:ident, $def_id:ident, $req:ident => ignore) => {
        if let Some(id) = $tcx.map.as_local_node_id($def_id) {
            $this.stack.borrow_mut().push((Request::$req, id));

            (id, ItemCtxt {
                tcx: $tcx,
                provider: $this,
                def_id: $def_id,
                last_incomplete: Cell::new(None)
            })
        } else {
            return Err(Unsupported);
        }
    };
    ($this:ident, $tcx:ident, $def_id:ident, $req:ident => $fallback:expr) => {
        if let Some(id) = $tcx.map.as_local_node_id($def_id) {
            if !$this.cycle_check($tcx, Request::$req, id) {
                $fallback
            }

            (id, ItemCtxt {
                tcx: $tcx,
                provider: $this,
                def_id: $def_id,
                last_incomplete: Cell::new(None)
            })
        } else {
            return Err(Unsupported);
        }
    }
}

impl<'tcx> Provider<'tcx> for TypeckProvider<'tcx> {
    fn associated_item<'a>(&self, tcx: TyCtxt<'a, 'tcx, 'tcx>, def_id: DefId)
                           -> Result<ty::AssociatedItem, Unsupported> {
        use rustc::hir::*;
        use rustc::hir::map::*;
        let (id, _icx) = enter!(self, tcx, def_id, Leaf => bug!());

        let parent_id = tcx.map.get_parent(id);
        let parent_def_id = tcx.map.local_def_id(parent_id);
        let item = match tcx.map.get(id) {
            NodeTraitItem(trait_item) => {
                let (kind, has_self, has_value) = match trait_item.node {
                    MethodTraitItem(ref sig, ref body) => {
                        (ty::AssociatedKind::Method, sig.decl.get_self().is_some(),
                         body.is_some())
                    }
                    ConstTraitItem(_, ref value) => {
                        (ty::AssociatedKind::Const, false, value.is_some())
                    }
                    TypeTraitItem(_, ref ty) => {
                        (ty::AssociatedKind::Type, false, ty.is_some())
                    }
                };

                ty::AssociatedItem {
                    name: trait_item.name,
                    kind: kind,
                    vis: ty::Visibility::from_hir(&Inherited, id, tcx),
                    defaultness: Defaultness::Default,
                    has_value: has_value,
                    def_id: def_id,
                    container: ty::TraitContainer(parent_def_id),
                    method_has_self_argument: has_self
                }
            }
            NodeImplItem(impl_item) => {
                let (kind, has_self) = match impl_item.node {
                    ImplItemKind::Method(ref sig, _) => {
                        (ty::AssociatedKind::Method, sig.decl.get_self().is_some())
                    }
                    ImplItemKind::Const(..) => (ty::AssociatedKind::Const, false),
                    ImplItemKind::Type(..) => (ty::AssociatedKind::Type, false)
                };

                // Trait impl items are always public.
                let public = Visibility::Public;
                let parent_item = tcx.map.expect_item(parent_id);
                let vis = if let ItemImpl(.., Some(_), _, _) = parent_item.node {
                    &public
                } else {
                    &impl_item.vis
                };

                ty::AssociatedItem {
                    name: impl_item.name,
                    kind: kind,
                    vis: ty::Visibility::from_hir(vis, id, tcx),
                    defaultness: impl_item.defaultness,
                    has_value: true,
                    def_id: def_id,
                    container: ty::ImplContainer(parent_def_id),
                    method_has_self_argument: has_self
                }
            }
            _ => return Err(Unsupported)
        };
        tcx.associated_items.borrow_mut().insert(def_id, item);
        Ok(item)
    }

    fn associated_item_def_ids<'a>(&self, tcx: TyCtxt<'a, 'tcx, 'tcx>, def_id: DefId)
                                   -> Result<Rc<Vec<DefId>>, Unsupported> {
        use rustc::hir::*;
        let (id, _icx) = enter!(self, tcx, def_id, Leaf => bug!());

        let items: Vec<_> = match tcx.map.expect_item(id).node {
            ItemTrait(.., ref trait_items) => {
                trait_items.iter().map(|trait_item| {
                    tcx.map.local_def_id(trait_item.id)
                }).collect()
            }
            ItemImpl(.., ref impl_items) => {
                impl_items.iter().map(|impl_item| {
                    tcx.map.local_def_id(impl_item.id)
                }).collect()
            }
            _ => return Err(Unsupported)
        };
        let items = Rc::new(items);
        tcx.associated_item_def_ids.borrow_mut().insert(def_id, items.clone());
        Ok(items)
    }

    fn trait_def<'a>(&self, tcx: TyCtxt<'a, 'tcx, 'tcx>, def_id: DefId)
                     -> Result<&'tcx ty::TraitDef, Unsupported> {
        use rustc::hir::*;
        let (id, _icx) = enter!(self, tcx, def_id, Leaf => bug!());

        let item = tcx.map.expect_item(id);
        let unsafety = match item.node {
            ItemTrait(unsafety, ..) => unsafety,
            _ => return Err(Unsupported)
        };

        let paren_sugar = tcx.has_attr(def_id, "rustc_paren_sugar");
        if paren_sugar && !tcx.sess.features.borrow().unboxed_closures {
            let mut err = tcx.sess.struct_span_err(
                item.span,
                "the `#[rustc_paren_sugar]` attribute is a temporary means of controlling \
                which traits can use parenthetical notation");
            help!(&mut err,
                "add `#![feature(unboxed_closures)]` to \
                the crate attributes to use it");
            err.emit();
        }

        let def_path_hash = tcx.def_path(def_id).deterministic_hash(tcx);
        let def = ty::TraitDef::new(def_id, unsafety, paren_sugar, def_path_hash);
        let def = tcx.alloc_trait_def(def);
        tcx.trait_defs.borrow_mut().insert(def_id, def);
        Ok(def)
    }

    fn adt_def<'a>(&self, tcx: TyCtxt<'a, 'tcx, 'tcx>, def_id: DefId)
                   -> Result<&'tcx ty::AdtDef, Unsupported> {
        use rustc::hir::*;
        use rustc::hir::map::*;
        let mut ignore_discriminants = false;
        let (id, _icx) = enter!(self, tcx, def_id, AdtDef => ignore_discriminants = true);

        let node = tcx.map.get(id);
        let item = match node {
            NodeStructCtor(_) => {
                return Ok(tcx.lookup_adt_def(tcx.map.get_parent_did(id)));
            }
            NodeItem(item) => item,
            _ => return Err(Unsupported)
        };

        let (kind, variants) = match item.node {
            ItemStruct(ref def, _) => {
                // Use separate constructor id for unit/tuple structs
                // and reuse did for braced structs.
                let ctor_id = if !def.is_struct() {
                    tcx.map.local_def_id(def.id())
                } else {
                    def_id
                };
                (ty::AdtKind::Struct, vec![convert_variant(tcx, ctor_id, item.name,
                                                           ConstInt::Infer(0), def)])
            }
            ItemUnion(ref def, _) => {
                (ty::AdtKind::Union, vec![convert_variant(tcx, def_id, item.name,
                                                          ConstInt::Infer(0), def)])
            }
            ItemEnum(ref def, _) => {
                let repr_hints = tcx.lookup_repr_hints(def_id);
                let repr_type = tcx.enum_repr_type(repr_hints.get(0));
                let initial = repr_type.initial_discriminant(tcx);
                let mut prev_discr = None::<ty::Disr>;
                (ty::AdtKind::Enum, def.variants.iter().map(|v| {
                    let wrapped_discr = prev_discr.map_or(initial, |d| d.wrap_incr());
                    let discr_expr = if ignore_discriminants {
                        None
                    } else {
                        v.node.disr_expr.as_ref()
                    };
                    let discr = if let Some(e) = discr_expr {
                        evaluate_discr_expr(tcx, repr_type, e)
                    } else if let Some(discr) = repr_type.disr_incr(tcx, prev_discr) {
                        Some(discr)
                    } else {
                        struct_span_err!(tcx.sess, v.span, E0370,
                                         "enum discriminant overflowed")
                            .span_label(v.span, &format!("overflowed on value after {}",
                                                         prev_discr.unwrap()))
                            .note(&format!("explicitly set `{} = {}` if that is desired outcome",
                                           v.node.name, wrapped_discr))
                            .emit();
                        None
                    }.unwrap_or(wrapped_discr);
                    prev_discr = Some(discr);

                    let vid = tcx.map.local_def_id(v.node.data.id());
                    convert_variant(tcx, vid, v.node.name, discr, &v.node.data)
                }).collect())
            }
            _ => return Err(Unsupported)
        };

        let adt = tcx.alloc_adt_def(def_id, kind, variants);
        tcx.adt_defs.borrow_mut().insert(def_id, adt);
        Ok(adt)
    }

    fn generics<'a>(&self, tcx: TyCtxt<'a, 'tcx, 'tcx>, def_id: DefId)
                    -> Result<&'tcx ty::Generics<'tcx>, Unsupported> {
        use rustc::hir::*;
        use rustc::hir::map::*;
        let (id, icx) = enter!(self, tcx, def_id, Generics => ignore);

        let node = tcx.map.get(id);
        let parent_def_id = match node {
            NodeImplItem(_) |
            NodeTraitItem(_) |
            NodeVariant(_) |
            NodeStructCtor(_) |
            NodeField(_) => {
                let parent_id = tcx.map.get_parent(id);
                Some(tcx.map.local_def_id(parent_id))
            }
            _ => None
        };

        let mut opt_self = None;
        let mut allow_defaults = false;

        let no_generics = Generics::empty();
        let ast_generics = match node {
            NodeTraitItem(item) => {
                match item.node {
                    MethodTraitItem(ref sig, _) => &sig.generics,
                    _ => &no_generics
                }
            }

            NodeImplItem(item) => {
                match item.node {
                    ImplItemKind::Method(ref sig, _) => &sig.generics,
                    _ => &no_generics
                }
            }

            NodeItem(item) => {
                match item.node {
                    ItemFn(.., ref generics, _) |
                    ItemImpl(_, _, ref generics, ..) => generics,

                    ItemTy(_, ref generics) |
                    ItemEnum(_, ref generics) |
                    ItemStruct(_, ref generics) |
                    ItemUnion(_, ref generics) => {
                        allow_defaults = true;
                        generics
                    }

                    ItemTrait(_, ref generics, ..) => {
                        // Add in the self type parameter.
                        //
                        // Something of a hack: use the node id for the trait, also as
                        // the node id for the Self type parameter.
                        let param_id = item.id;

                        let parent = tcx.map.get_parent(param_id);

                        let def = ty::TypeParameterDef {
                            index: 0,
                            name: keywords::SelfType.name(),
                            def_id: tcx.map.local_def_id(param_id),
                            default_def_id: tcx.map.local_def_id(parent),
                            default: None,
                            object_lifetime_default: ty::ObjectLifetimeDefault::BaseDefault,
                            pure_wrt_drop: false,
                        };
                        tcx.ty_param_defs.borrow_mut().insert(param_id, def.clone());
                        opt_self = Some(def);

                        allow_defaults = true;
                        generics
                    }

                    _ => &no_generics
                }
            }

            NodeForeignItem(item) => {
                match item.node {
                    ForeignItemStatic(..) => &no_generics,
                    ForeignItemFn(_, ref generics) => generics
                }
            }

            _ => &no_generics
        };

        let has_self = opt_self.is_some();
        let mut parent_has_self = false;
        let mut own_start = has_self as u32;
        let (parent_regions, parent_types) = parent_def_id.map_or((0, 0), |def_id| {
            let generics = tcx.item_generics(def_id);
            assert_eq!(generics.parent, None);
            assert_eq!(generics.parent_regions, 0);
            assert_eq!(generics.parent_types, 0);
            assert_eq!(has_self, false);
            parent_has_self = generics.has_self;
            own_start = generics.count() as u32;
            (generics.regions.len() as u32, generics.types.len() as u32)
        });

        let early_lifetimes = ast_generics.lifetimes.iter()
            .filter(|l| !tcx.named_region_map.late_bound.contains_key(&l.lifetime.id));
        let regions = early_lifetimes.enumerate().map(|(i, l)| {
            ty::RegionParameterDef {
                name: l.lifetime.name,
                index: own_start + i as u32,
                def_id: tcx.map.local_def_id(l.lifetime.id),
                bounds: l.bounds.iter().map(|l| {
                    ast_region_to_region(tcx, l)
                }).collect(),
                pure_wrt_drop: l.pure_wrt_drop,
            }
        }).collect::<Vec<_>>();

        // Now create the real type parameters.
        let type_start = own_start + regions.len() as u32;
        let types = ast_generics.ty_params.iter().enumerate();
        let types: Vec<_> = opt_self.into_iter().chain(types.map(|(i, param)| {
            let i = type_start + i as u32;
            tcx.ty_param_defs.memoize(param.id, || {
                let default = param.default.as_ref()
                    .map(|def| icx.to_ty(&ExplicitRscope, def));

                let object_lifetime_default =
                    compute_object_lifetime_default(tcx, param.id,
                                                    &param.bounds, &ast_generics.where_clause);

                let parent = tcx.map.get_parent(param.id);

                if !allow_defaults && default.is_some() {
                    if !tcx.sess.features.borrow().default_type_parameter_fallback {
                        tcx.sess.add_lint(
                            lint::builtin::INVALID_TYPE_PARAM_DEFAULT,
                            param.id,
                            param.span,
                            format!("defaults for type parameters are only allowed in `struct`, \
                                     `enum`, `type`, or `trait` definitions."));
                    }
                }

                if param.name == keywords::SelfType.name() {
                    span_bug!(param.span, "`Self` should not be the name of a type parameter");
                }

                ty::TypeParameterDef {
                    index: i,
                    name: param.name,
                    def_id: tcx.map.local_def_id(param.id),
                    default_def_id: tcx.map.local_def_id(parent),
                    default: default,
                    object_lifetime_default: object_lifetime_default,
                    pure_wrt_drop: param.pure_wrt_drop,
                }
            })
        })).collect();

        // Debugging aid.
        if tcx.has_attr(def_id, "rustc_object_lifetime_default") {
            let object_lifetime_default_reprs: String =
                types.iter().map(|t| {
                    match t.object_lifetime_default {
                        ty::ObjectLifetimeDefault::Specific(r) => r.to_string(),
                        d => format!("{:?}", d),
                    }
                }).collect::<Vec<String>>().join(",");
            tcx.sess.span_err(tcx.map.span(id), &object_lifetime_default_reprs);
        }

        let generics = tcx.alloc_generics(ty::Generics {
            parent: parent_def_id,
            parent_regions: parent_regions,
            parent_types: parent_types,
            regions: regions,
            types: types,
            has_self: has_self || parent_has_self
        });

        if icx.sanitize(generics.types.iter().filter_map(|def| def.default.as_ref())) {
            tcx.generics.borrow_mut().insert(def_id, generics);
        }
        Ok(generics)
    }

    fn super_predicates<'a>(&self, tcx: TyCtxt<'a, 'tcx, 'tcx>, def_id: DefId)
                            -> Result<Rc<ty::GenericPredicates<'tcx>>, Unsupported> {
        use rustc::hir::*;
        let (id, icx) = enter!(self, tcx, def_id, SuperPredicates => return {
            Ok(Rc::new(ty::GenericPredicates {
                parent: None,
                predicates: vec![]
            }))
        });

        let item = tcx.map.expect_item(id);
        let (generics, supertraits) = match item.node {
            ItemTrait(_, ref generics, ref supertraits, _) => (generics, supertraits),
            _ => return Err(Unsupported)
        };

        // Convert the bounds that follow the colon, e.g. `Bar+Zed` in `trait Foo : Bar+Zed`.
        let self_param_ty = tcx.mk_self_type();
        let superbounds1 = AstConv::compute_bounds(&icx,
                                                   self_param_ty,
                                                   supertraits,
                                                   SizedByDefault::No,
                                                   None,
                                                   item.span);

        let superbounds1 = superbounds1.predicates(tcx, self_param_ty);

        // Convert any explicit superbounds in the where clause,
        // e.g. `trait Foo where Self : Bar`:
        let superbounds2 =
            generics.where_clause
                .predicates
                .iter()
                .filter_map(|wp| match *wp {
                    WherePredicate::BoundPredicate(ref bp) => Some(bp),
                    _ => None
                })
                .filter(|bp| is_param(tcx, &bp.bounded_ty, id))
                .flat_map(|bp| bp.bounds.iter())
                .flat_map(|b| predicates_from_bound(&icx, self_param_ty, b));

        // Combine the two lists to form the complete set of superbounds:
        let superbounds = superbounds1.into_iter().chain(superbounds2).collect();
        let superpredicates = Rc::new(ty::GenericPredicates {
            parent: None,
            predicates: superbounds
        });
        debug!("superpredicates for trait {:?} = {:?}", def_id, superpredicates);

        // Force cycles through traits' supertraits to be revealed.
        for predicate in &superpredicates.predicates {
            if let Some(tr) = predicate.to_opt_poly_trait_ref() {
                tcx.item_super_predicates(tr.def_id());
            }
        }

        tcx.super_predicates.borrow_mut().insert(def_id, superpredicates.clone());
        Ok(superpredicates)
    }

    fn predicates<'a>(&self, tcx: TyCtxt<'a, 'tcx, 'tcx>, def_id: DefId)
                      -> Result<Rc<ty::GenericPredicates<'tcx>>, Unsupported> {
        use rustc::hir::*;
        use rustc::hir::map::*;
        let (id, icx) = enter!(self, tcx, def_id, Predicates => ignore);

        let mut trait_items = &[][..];
        let mut predicates = vec![];

        let no_generics = Generics::empty();
        let ast_generics = match tcx.map.get(id) {
            NodeTraitItem(item) => {
                match item.node {
                    MethodTraitItem(ref sig, _) => &sig.generics,
                    _ => &no_generics
                }
            }

            NodeImplItem(item) => {
                match item.node {
                    ImplItemKind::Method(ref sig, _) => &sig.generics,
                    _ => &no_generics
                }
            }

            NodeItem(item) => {
                match item.node {
                    ItemFn(.., ref generics, _) |
                    ItemImpl(_, _, ref generics, ..) |
                    ItemTy(_, ref generics) |
                    ItemEnum(_, ref generics) |
                    ItemStruct(_, ref generics) |
                    ItemUnion(_, ref generics) => {
                        generics
                    }

                    ItemTrait(_, ref generics, _, ref items) => {
                        trait_items = items;
                        predicates = tcx.item_super_predicates(def_id).predicates.clone();

                        // Add in a predicate that `Self:Trait` (where `Trait` is the
                        // current trait).  This is needed for builtin bounds.
                        let trait_ref = ty::TraitRef {
                            def_id: def_id,
                            substs: Substs::identity_for_item(tcx, def_id)
                        };
                        let self_predicate = trait_ref.to_poly_trait_ref().to_predicate();
                        predicates.push(self_predicate);

                        generics
                    }

                    _ => &no_generics
                }
            }

            NodeForeignItem(item) => {
                match item.node {
                    ForeignItemStatic(..) => &no_generics,
                    ForeignItemFn(_, ref generics) => generics
                }
            }

            _ => &no_generics
        };

        let generics = tcx.item_generics(def_id);
        let mut has_self = generics.has_self;
        let parent_count = generics.parent.map_or(0, |def_id| {
            let generics = tcx.item_generics(def_id);
            assert_eq!(generics.parent, None);
            assert_eq!(generics.parent_regions, 0);
            assert_eq!(generics.parent_types, 0);
            has_self = false;
            generics.count() as u32
        });

        // Collect the region predicates that were declared inline as
        // well. In the case of parameters declared on a fn or method, we
        // have to be careful to only iterate over early-bound regions.
        let own_start = parent_count + has_self as u32;
        let early_lifetimes = ast_generics.lifetimes.iter()
            .filter(|l| !tcx.named_region_map.late_bound.contains_key(&l.lifetime.id));
        for (index, param) in early_lifetimes.enumerate() {
            let index = own_start + index as u32;
            let region = tcx.mk_region(ty::ReEarlyBound(ty::EarlyBoundRegion {
                index: index,
                name: param.lifetime.name
            }));
            for bound in &param.bounds {
                let bound_region = ast_region_to_region(tcx, bound);
                let outlives = ty::Binder(ty::OutlivesPredicate(region, bound_region));
                predicates.push(outlives.to_predicate());
            }
        }

        // Collect the predicates that were written inline by the user on each
        // type parameter (e.g., `<T:Foo>`).
        let type_start = own_start + generics.regions.len() as u32;
        for (index, param) in ast_generics.ty_params.iter().enumerate() {
            let index = type_start + index as u32;
            let param_ty = ty::ParamTy::new(index, param.name).to_ty(tcx);
            let bounds = AstConv::compute_bounds(&icx,
                                                 param_ty,
                                                 &param.bounds,
                                                 SizedByDefault::Yes,
                                                 None,
                                                 param.span);
            predicates.extend(bounds.predicates(tcx, param_ty));
        }

        // Add in the bounds that appear in the where-clause
        let where_clause = &ast_generics.where_clause;
        for predicate in &where_clause.predicates {
            match predicate {
                &WherePredicate::BoundPredicate(ref bound_pred) => {
                    let ty = AstConv::ast_ty_to_ty(&icx,
                                                   &ExplicitRscope,
                                                   &bound_pred.bounded_ty);

                    for bound in bound_pred.bounds.iter() {
                        match bound {
                            &TyParamBound::TraitTyParamBound(ref poly_trait_ref, _) => {
                                let mut projections = Vec::new();

                                let trait_ref =
                                    AstConv::instantiate_poly_trait_ref(&icx,
                                                                        &ExplicitRscope,
                                                                        poly_trait_ref,
                                                                        ty,
                                                                        &mut projections);

                                predicates.push(trait_ref.to_predicate());

                                for projection in &projections {
                                    predicates.push(projection.to_predicate());
                                }
                            }

                            &TyParamBound::RegionTyParamBound(ref lifetime) => {
                                let region = ast_region_to_region(tcx, lifetime);
                                let pred = ty::Binder(ty::OutlivesPredicate(ty, region));
                                predicates.push(ty::Predicate::TypeOutlives(pred))
                            }
                        }
                    }
                }

                &WherePredicate::RegionPredicate(ref region_pred) => {
                    let r1 = ast_region_to_region(tcx, &region_pred.lifetime);
                    for bound in &region_pred.bounds {
                        let r2 = ast_region_to_region(tcx, bound);
                        let pred = ty::Binder(ty::OutlivesPredicate(r1, r2));
                        predicates.push(ty::Predicate::RegionOutlives(pred))
                    }
                }

                &WherePredicate::EqPredicate(ref eq_pred) => {
                    // FIXME(#20041)
                    span_bug!(eq_pred.span,
                            "Equality constraints are not yet \
                            implemented (#20041)")
                }
            }
        }

        // Add trait bounds that come from associated items.
        predicates.extend(trait_items.iter().flat_map(|trait_item| {
            let bounds = match trait_item.node {
                TypeTraitItem(ref bounds, _) => bounds,
                _ => return vec![].into_iter()
            };

            let trait_ref = ty::TraitRef {
                def_id: def_id,
                substs: Substs::identity_for_item(tcx, def_id)
            };
            let assoc_ty = tcx.mk_projection(trait_ref, trait_item.name);

            let bounds = AstConv::compute_bounds(&icx,
                                                 assoc_ty,
                                                 bounds,
                                                 SizedByDefault::Yes,
                                                 None,
                                                 trait_item.span);

            bounds.predicates(tcx, assoc_ty).into_iter()
        }));

        let predicates = Rc::new(ty::GenericPredicates {
            parent: generics.parent,
            predicates: predicates
        });

        if icx.sanitize(predicates.predicates.iter()) {
            tcx.predicates.borrow_mut().insert(def_id, predicates.clone());
        }
        Ok(predicates)
    }

    fn ty<'a>(&self, tcx: TyCtxt<'a, 'tcx, 'tcx>, def_id: DefId)
              -> Result<Ty<'tcx>, Unsupported> {
        use rustc::hir::*;
        use rustc::hir::map::*;
        let (id, icx) = enter!(self, tcx, def_id, Type => ignore);

        let anon_scope = Some(AnonTypeScope::new(def_id));
        let ty = match tcx.map.get(id) {
            NodeTraitItem(item) => {
                match item.node {
                    MethodTraitItem(ref sig, _) => {
                        let self_ty = tcx.mk_self_type();
                        let fty = AstConv::ty_of_method(&icx, sig, self_ty, None);
                        let substs = Substs::identity_for_item(tcx, def_id);
                        tcx.mk_fn_def(def_id, substs, fty)
                    }
                    ConstTraitItem(ref ty, _) |
                    TypeTraitItem(_, Some(ref ty)) => {
                        icx.to_ty(&ExplicitRscope, ty)
                    }
                    TypeTraitItem(_, None) => return Err(Unsupported)
                }
            }

            NodeImplItem(item) => {
                match item.node {
                    ImplItemKind::Method(ref sig, _) => {
                        let self_ty = tcx.item_type(tcx.map.get_parent_did(id));
                        let fty = AstConv::ty_of_method(&icx, sig, self_ty, anon_scope);
                        let substs = Substs::identity_for_item(tcx, def_id);
                        tcx.mk_fn_def(def_id, substs, fty)
                    }
                    hir::ImplItemKind::Const(ref ty, _) => icx.to_ty(&ExplicitRscope, ty),
                    hir::ImplItemKind::Type(ref ty) => {
                        if tcx.impl_trait_ref(tcx.map.get_parent_did(id)).is_none() {
                            span_err!(tcx.sess, item.span, E0202,
                                      "associated types are not allowed in inherent impls");
                        }

                        icx.to_ty(&ExplicitRscope, ty)
                    }
                }
            }

            NodeItem(item) => {
                match item.node {
                    ItemStatic(ref ty, ..) | ItemConst(ref ty, _) => {
                        icx.to_ty(&StaticRscope::new(&tcx), ty)
                    }
                    ItemFn(ref decl, unsafety, _, abi, _, _) => {
                        let fty = AstConv::ty_of_bare_fn(&icx, unsafety, abi, &decl, anon_scope);
                        let substs = Substs::identity_for_item(tcx, def_id);
                        tcx.mk_fn_def(def_id, substs, fty)
                    }
                    ItemEnum(..) |
                    ItemStruct(..) |
                    ItemUnion(..) => {
                        let def = tcx.lookup_adt_def(def_id);
                        let substs = Substs::identity_for_item(tcx, def_id);
                        tcx.mk_adt(def, substs)
                    }
                    ItemTy(ref ty, _) |
                    ItemImpl(.., ref ty, _) => {
                        icx.to_ty(&ExplicitRscope, ty)
                    }
                    ItemDefaultImpl(..) |
                    ItemTrait(..) |
                    ItemMod(..) |
                    ItemForeignMod(..) |
                    ItemExternCrate(..) |
                    ItemUse(..) => return Err(Unsupported)
                }
            }

            NodeForeignItem(foreign_item) => {
                match foreign_item.node {
                    ForeignItemFn(ref decl, _) => {
                        let abi = tcx.map.get_foreign_abi(id);
                        let fty = AstConv::ty_of_bare_fn(&icx, Unsafety::Unsafe, abi, decl, None);
                        let substs = Substs::identity_for_item(tcx, def_id);
                        tcx.mk_fn_def(def_id, substs, fty)
                    }
                    ForeignItemStatic(ref ty, _) => icx.to_ty(&ExplicitRscope, ty),
                }
            }

            NodeStructCtor(&ref def) |
            NodeVariant(&Spanned { node: hir::Variant_ { data: ref def, .. }, .. }) => {
                let ty = tcx.item_type(tcx.map.get_parent_did(id));
                match *def {
                    VariantData::Unit(..) | VariantData::Struct(..) => ty,
                    VariantData::Tuple(ref fields, _) => {
                        let inputs: Vec<_> = fields.iter().map(|field| {
                            tcx.item_type(tcx.map.local_def_id(field.id))
                        }).collect();
                        let substs = Substs::identity_for_item(tcx, def_id);
                        tcx.mk_fn_def(def_id, substs, tcx.mk_bare_fn(ty::BareFnTy {
                            unsafety: Unsafety::Normal,
                            abi: abi::Abi::Rust,
                            sig: ty::Binder(ty::FnSig {
                                inputs: inputs,
                                output: ty,
                                variadic: false
                            })
                        }))
                    }
                }
            }

            NodeField(field) => icx.to_ty(&ExplicitRscope, &field.ty),

            _ => return Err(Unsupported)
        };

        if icx.sanitize(iter::once(&ty)) {
            tcx.item_types.borrow_mut().insert(def_id, ty);
        }
        Ok(ty)
    }

    fn impl_trait_ref<'a>(&self, tcx: TyCtxt<'a, 'tcx, 'tcx>, def_id: DefId)
                          -> Result<Option<ty::TraitRef<'tcx>>, Unsupported> {
        use rustc::hir::*;
        let (id, icx) = enter!(self, tcx, def_id, ImplTraitRef => ignore);

        let trait_ref = match tcx.map.expect_item(id).node {
            ItemDefaultImpl(_, ref ast_trait_ref) => {
                Some(AstConv::instantiate_mono_trait_ref(&icx,
                                                         &ExplicitRscope,
                                                         ast_trait_ref,
                                                         tcx.mk_self_type()))
            }

            ItemImpl(.., ref opt_trait_ref, _, _) => {
                opt_trait_ref.as_ref().map(|ast_trait_ref| {
                    AstConv::instantiate_mono_trait_ref(&icx,
                                                        &ExplicitRscope,
                                                        ast_trait_ref,
                                                        tcx.item_type(def_id))
                })
            }

            _ => return Err(Unsupported)
        };

        if icx.sanitize(iter::once(&trait_ref)) {
            tcx.impl_trait_refs.borrow_mut().insert(def_id, trait_ref);
        }
        Ok(trait_ref)
    }
}
