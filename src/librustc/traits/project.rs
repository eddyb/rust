// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Code for projecting associated types out of trait references.

use super::elaborate_predicates;
use super::specialization_graph;
use super::translate_substs;
use super::Obligation;
use super::ObligationCause;
use super::PredicateObligation;
use super::SelectionContext;
use super::SelectionError;
use super::VtableClosureData;
use super::VtableGeneratorData;
use super::VtableFnPointerData;
use super::VtableImplData;
use super::util;

use hir::def_id::DefId;
use infer::InferOk;
use infer::type_variable::TypeVariableOrigin;
use middle::const_val::ConstVal;
use rustc_data_structures::snapshot_map::{Snapshot, SnapshotMap};
use syntax::ast;
use syntax::symbol::Symbol;
use ty::subst::{Subst, Substs};
use ty::{self, ToPredicate, ToPolyTraitRef, Ty, TyCtxt};
use ty::fold::{TypeFoldable, TypeFolder};
use util::common::FN_OUTPUT_NAME;

/// Depending on the stage of compilation, we want projection to be
/// more or less conservative.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Reveal {
    /// At type-checking time, we refuse to project any associated
    /// type that is marked `default`. Non-`default` ("final") types
    /// are always projected. This is necessary in general for
    /// soundness of specialization. However, we *could* allow
    /// projections in fully-monomorphic cases. We choose not to,
    /// because we prefer for `default type` to force the type
    /// definition to be treated abstractly by any consumers of the
    /// impl. Concretely, that means that the following example will
    /// fail to compile:
    ///
    /// ```
    /// trait Assoc {
    ///     type Output;
    /// }
    ///
    /// impl<T> Assoc for T {
    ///     default type Output = bool;
    /// }
    ///
    /// fn main() {
    ///     let <() as Assoc>::Output = true;
    /// }
    UserFacing,

    /// At trans time, all monomorphic projections will succeed.
    /// Also, `impl Trait` is normalized to the concrete type,
    /// which has to be already collected by type-checking.
    ///
    /// NOTE: As `impl Trait`'s concrete type should *never*
    /// be observable directly by the user, `Reveal::All`
    /// should not be used by checks which may expose
    /// type equality or type contents to the user.
    /// There are some exceptions, e.g. around OIBITS and
    /// transmute-checking, which expose some details, but
    /// not the whole concrete type of the `impl Trait`.
    All,
}

pub type PolyProjectionObligation<'tcx> =
    Obligation<'tcx, ty::PolyProjectionPredicate<'tcx>>;

pub type ProjectionObligation<'tcx> =
    Obligation<'tcx, ty::ProjectionPredicate<'tcx>>;

pub type ProjectionTyObligation<'tcx> =
    Obligation<'tcx, ty::ProjectionTy<'tcx>>;

/// When attempting to resolve `<T as TraitRef>::Name` ...
#[derive(Debug)]
pub enum ProjectionTyError<'tcx> {
    /// ...we found multiple sources of information and couldn't resolve the ambiguity.
    TooManyCandidates,

    /// ...an error occurred matching `T : TraitRef`
    TraitSelectionError(SelectionError<'tcx>),
}

#[derive(Clone)]
pub struct MismatchedProjectionTypes<'tcx> {
    pub err: ty::error::TypeError<'tcx>
}

#[derive(PartialEq, Eq, Debug)]
enum ProjectionTyCandidate<'tcx> {
    // from a where-clause in the env or object type
    ParamEnv(ty::PolyProjectionPredicate<'tcx>),

    // from the definition of `Trait` when you have something like <<A as Trait>::B as Trait2>::C
    TraitDef(ty::PolyProjectionPredicate<'tcx>),

    // from a "impl" (or a "pseudo-impl" returned by select)
    Select,
}

struct ProjectionTyCandidateSet<'tcx> {
    vec: Vec<ProjectionTyCandidate<'tcx>>,
    ambiguous: bool
}

/// Evaluates constraints of the form:
///
///     for<...> <T as Trait>::U == V
///
/// If successful, this may result in additional obligations. Also returns
/// the projection cache key used to track these additional obligations.
pub fn poly_project_and_unify_type<'cx, 'gcx, 'tcx>(
    selcx: &mut SelectionContext<'cx, 'gcx, 'tcx>,
    obligation: &PolyProjectionObligation<'tcx>)
    -> Result<Option<Vec<PredicateObligation<'tcx>>>,
              MismatchedProjectionTypes<'tcx>>
{
    debug!("poly_project_and_unify_type(obligation={:?})",
           obligation);

    let infcx = selcx.infcx();
    infcx.commit_if_ok(|snapshot| {
        let (skol_predicate, skol_map) =
            infcx.skolemize_late_bound_regions(&obligation.predicate, snapshot);

        let skol_obligation = obligation.with(skol_predicate);
        let r = match project_and_unify_type(selcx, &skol_obligation) {
            Ok(result) => {
                let span = obligation.cause.span;
                match infcx.leak_check(false, span, &skol_map, snapshot) {
                    Ok(()) => Ok(infcx.plug_leaks(skol_map, snapshot, result)),
                    Err(e) => Err(MismatchedProjectionTypes { err: e }),
                }
            }
            Err(e) => {
                Err(e)
            }
        };

        r
    })
}

/// Evaluates constraints of the form:
///
///     <T as Trait>::U == V
///
/// If successful, this may result in additional obligations.
fn project_and_unify_type<'cx, 'gcx, 'tcx>(
    selcx: &mut SelectionContext<'cx, 'gcx, 'tcx>,
    obligation: &ProjectionObligation<'tcx>)
    -> Result<Option<Vec<PredicateObligation<'tcx>>>,
              MismatchedProjectionTypes<'tcx>>
{
    debug!("project_and_unify_type(obligation={:?})",
           obligation);

    let Normalized { value: normalized_ty, mut obligations } =
        match opt_normalize_projection_type(selcx,
                                            obligation.param_env,
                                            obligation.predicate.projection_ty,
                                            obligation.cause.clone(),
                                            obligation.recursion_depth) {
            Some(n) => n,
            None => return Ok(None),
        };

    debug!("project_and_unify_type: normalized_ty={:?} obligations={:?}",
           normalized_ty,
           obligations);

    let infcx = selcx.infcx();
    match infcx.at(&obligation.cause, obligation.param_env)
               .eq(normalized_ty, obligation.predicate.ty) {
        Ok(InferOk { obligations: inferred_obligations, value: () }) => {
            obligations.extend(inferred_obligations);
            Ok(Some(obligations))
        },
        Err(err) => Err(MismatchedProjectionTypes { err: err }),
    }
}

/// Normalizes any associated type projections in `value`, replacing
/// them with a fully resolved type where possible. The return value
/// combines the normalized result and any additional obligations that
/// were incurred as result.
pub fn normalize<'a, 'b, 'gcx, 'tcx, T>(selcx: &'a mut SelectionContext<'b, 'gcx, 'tcx>,
                                        param_env: ty::ParamEnv<'tcx>,
                                        cause: ObligationCause<'tcx>,
                                        value: &T)
                                        -> Normalized<'tcx, T>
    where T : TypeFoldable<'tcx>
{
    normalize_with_depth(selcx, param_env, cause, 0, value)
}

/// As `normalize`, but with a custom depth.
pub fn normalize_with_depth<'a, 'b, 'gcx, 'tcx, T>(
    selcx: &'a mut SelectionContext<'b, 'gcx, 'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    cause: ObligationCause<'tcx>,
    depth: usize,
    value: &T)
    -> Normalized<'tcx, T>

    where T : TypeFoldable<'tcx>
{
    debug!("normalize_with_depth(depth={}, value={:?})", depth, value);
    let mut normalizer = AssociatedTypeNormalizer::new(selcx, param_env, cause, depth);
    let result = normalizer.fold(value);
    debug!("normalize_with_depth: depth={} result={:?} with {} obligations",
           depth, result, normalizer.obligations.len());
    debug!("normalize_with_depth: depth={} obligations={:?}",
           depth, normalizer.obligations);
    Normalized {
        value: result,
        obligations: normalizer.obligations,
    }
}

struct AssociatedTypeNormalizer<'a, 'b: 'a, 'gcx: 'b+'tcx, 'tcx: 'b> {
    selcx: &'a mut SelectionContext<'b, 'gcx, 'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    cause: ObligationCause<'tcx>,
    obligations: Vec<PredicateObligation<'tcx>>,
    depth: usize,
}

impl<'a, 'b, 'gcx, 'tcx> AssociatedTypeNormalizer<'a, 'b, 'gcx, 'tcx> {
    fn new(selcx: &'a mut SelectionContext<'b, 'gcx, 'tcx>,
           param_env: ty::ParamEnv<'tcx>,
           cause: ObligationCause<'tcx>,
           depth: usize)
           -> AssociatedTypeNormalizer<'a, 'b, 'gcx, 'tcx>
    {
        AssociatedTypeNormalizer {
            selcx,
            param_env,
            cause,
            obligations: vec![],
            depth,
        }
    }

    fn fold<T:TypeFoldable<'tcx>>(&mut self, value: &T) -> T {
        let value = self.selcx.infcx().resolve_type_vars_if_possible(value);

        if !value.has_projections() {
            value.clone()
        } else {
            value.fold_with(self)
        }
    }
}

impl<'a, 'b, 'gcx, 'tcx> TypeFolder<'gcx, 'tcx> for AssociatedTypeNormalizer<'a, 'b, 'gcx, 'tcx> {
    fn tcx<'c>(&'c self) -> TyCtxt<'c, 'gcx, 'tcx> {
        self.selcx.tcx()
    }

    fn fold_ty(&mut self, ty: Ty<'tcx>) -> Ty<'tcx> {
        // We don't want to normalize associated types that occur inside of region
        // binders, because they may contain bound regions, and we can't cope with that.
        //
        // Example:
        //
        //     for<'a> fn(<T as Foo<&'a>>::A)
        //
        // Instead of normalizing `<T as Foo<&'a>>::A` here, we'll
        // normalize it when we instantiate those bound regions (which
        // should occur eventually).

        let ty = ty.super_fold_with(self);
        match ty.sty {
            ty::TyAnon(def_id, substs) if !substs.has_escaping_regions() => { // (*)
                // Only normalize `impl Trait` after type-checking, usually in trans.
                match self.param_env.reveal {
                    Reveal::UserFacing => ty,

                    Reveal::All => {
                        let generic_ty = self.tcx().type_of(def_id);
                        let concrete_ty = generic_ty.subst(self.tcx(), substs);
                        self.fold_ty(concrete_ty)
                    }
                }
            }

            ty::TyProjection(ref data) if !data.has_escaping_regions() => { // (*)

                // (*) This is kind of hacky -- we need to be able to
                // handle normalization within binders because
                // otherwise we wind up a need to normalize when doing
                // trait matching (since you can have a trait
                // obligation like `for<'a> T::B : Fn(&'a int)`), but
                // we can't normalize with bound regions in scope. So
                // far now we just ignore binders but only normalize
                // if all bound regions are gone (and then we still
                // have to renormalize whenever we instantiate a
                // binder). It would be better to normalize in a
                // binding-aware fashion.

                let Normalized { value: normalized_ty, obligations } =
                    normalize_projection_type(self.selcx,
                                              self.param_env,
                                              data.clone(),
                                              self.cause.clone(),
                                              self.depth);
                debug!("AssociatedTypeNormalizer: depth={} normalized {:?} to {:?} \
                        with {} add'l obligations",
                       self.depth, ty, normalized_ty, obligations.len());
                self.obligations.extend(obligations);
                normalized_ty
            }

            _ => {
                ty
            }
        }
    }

    fn fold_const(&mut self, constant: &'tcx ty::Const<'tcx>) -> &'tcx ty::Const<'tcx> {
        if let ConstVal::Unevaluated(def_id, substs) = constant.val {
            if substs.needs_infer() {
                let identity_substs = Substs::identity_for_item(self.tcx(), def_id);
                let data = self.param_env.and((def_id, identity_substs));
                match self.tcx().lift_to_global(&data) {
                    Some(data) => {
                        match self.tcx().const_eval(data) {
                            Ok(evaluated) => {
                                let evaluated = evaluated.subst(self.tcx(), substs);
                                return self.fold_const(evaluated);
                            }
                            Err(_) => {}
                        }
                    }
                    None => {}
                }
            } else {
                let data = self.param_env.and((def_id, substs));
                match self.tcx().lift_to_global(&data) {
                    Some(data) => {
                        match self.tcx().const_eval(data) {
                            Ok(evaluated) => return self.fold_const(evaluated),
                            Err(_) => {}
                        }
                    }
                    None => {}
                }
            }
        }
        constant
    }
}

#[derive(Clone)]
pub struct Normalized<'tcx,T> {
    pub value: T,
    pub obligations: Vec<PredicateObligation<'tcx>>,
}

pub type NormalizedTy<'tcx> = Normalized<'tcx, Ty<'tcx>>;

impl<'tcx,T> Normalized<'tcx,T> {
    pub fn with<U>(self, value: U) -> Normalized<'tcx,U> {
        Normalized { value: value, obligations: self.obligations }
    }
}

/// The guts of `normalize`: normalize a specific projection like `<T
/// as Trait>::Item`. The result is always a type (and possibly
/// additional obligations). If ambiguity arises, which implies that
/// there are unresolved type variables in the projection, we will
/// substitute a fresh type variable `$X` and generate a new
/// obligation `<T as Trait>::Item == $X` for later.
pub fn normalize_projection_type<'a, 'b, 'gcx, 'tcx>(
    selcx: &'a mut SelectionContext<'b, 'gcx, 'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    projection_ty: ty::ProjectionTy<'tcx>,
    cause: ObligationCause<'tcx>,
    depth: usize)
    -> NormalizedTy<'tcx>
{
    opt_normalize_projection_type(selcx, param_env, projection_ty.clone(), cause.clone(), depth)
        .unwrap_or_else(move || {
            // if we bottom out in ambiguity, create a type variable
            // and a deferred predicate to resolve this when more type
            // information is available.

            let tcx = selcx.infcx().tcx;
            let def_id = projection_ty.item_def_id;
            let ty_var = selcx.infcx().next_ty_var(
                TypeVariableOrigin::NormalizeProjectionType(tcx.def_span(def_id)));
            let projection = ty::Binder(ty::ProjectionPredicate {
                projection_ty,
                ty: ty_var
            });
            let obligation = Obligation::with_depth(
                cause, depth + 1, param_env, projection.to_predicate());
            Normalized {
                value: ty_var,
                obligations: vec![obligation]
            }
        })
}

/// The guts of `normalize`: normalize a specific projection like `<T
/// as Trait>::Item`. The result is always a type (and possibly
/// additional obligations). Returns `None` in the case of ambiguity,
/// which indicates that there are unbound type variables.
fn opt_normalize_projection_type<'a, 'b, 'gcx, 'tcx>(
    selcx: &'a mut SelectionContext<'b, 'gcx, 'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    projection_ty: ty::ProjectionTy<'tcx>,
    cause: ObligationCause<'tcx>,
    depth: usize)
    -> Option<NormalizedTy<'tcx>>
{
    let infcx = selcx.infcx();

    let projection_ty = infcx.resolve_type_vars_if_possible(&projection_ty);
    let cache_key = ProjectionCacheKey { ty: projection_ty };

    debug!("opt_normalize_projection_type(\
           projection_ty={:?}, \
           depth={})",
           projection_ty,
           depth);

    // FIXME(#20304) For now, I am caching here, which is good, but it
    // means we don't capture the type variables that are created in
    // the case of ambiguity. Which means we may create a large stream
    // of such variables. OTOH, if we move the caching up a level, we
    // would not benefit from caching when proving `T: Trait<U=Foo>`
    // bounds. It might be the case that we want two distinct caches,
    // or else another kind of cache entry.

    match infcx.projection_cache.borrow_mut().try_start(cache_key) {
        Ok(()) => { }
        Err(ProjectionCacheEntry::Ambiguous) => {
            // If we found ambiguity the last time, that generally
            // means we will continue to do so until some type in the
            // key changes (and we know it hasn't, because we just
            // fully resolved it). One exception though is closure
            // types, which can transition from having a fixed kind to
            // no kind with no visible change in the key.
            //
            // FIXME(#32286) refactor this so that closure type
            // changes
            debug!("opt_normalize_projection_type: \
                    found cache entry: ambiguous");
            if !projection_ty.has_closure_types() {
                return None;
            }
        }
        Err(ProjectionCacheEntry::InProgress) => {
            // If while normalized A::B, we are asked to normalize
            // A::B, just return A::B itself. This is a conservative
            // answer, in the sense that A::B *is* clearly equivalent
            // to A::B, though there may be a better value we can
            // find.

            // Under lazy normalization, this can arise when
            // bootstrapping.  That is, imagine an environment with a
            // where-clause like `A::B == u32`. Now, if we are asked
            // to normalize `A::B`, we will want to check the
            // where-clauses in scope. So we will try to unify `A::B`
            // with `A::B`, which can trigger a recursive
            // normalization. In that case, I think we will want this code:
            //
            // ```
            // let ty = selcx.tcx().mk_projection(projection_ty.item_def_id,
            //                                    projection_ty.substs;
            // return Some(NormalizedTy { value: v, obligations: vec![] });
            // ```

            debug!("opt_normalize_projection_type: \
                    found cache entry: in-progress");

            // But for now, let's classify this as an overflow:
            let recursion_limit = selcx.tcx().sess.recursion_limit.get();
            let obligation = Obligation::with_depth(cause.clone(),
                                                    recursion_limit,
                                                    param_env,
                                                    projection_ty);
            selcx.infcx().report_overflow_error(&obligation, false);
        }
        Err(ProjectionCacheEntry::NormalizedTy(ty)) => {
            // If we find the value in the cache, then return it along
            // with the obligations that went along with it. Note
            // that, when using a fulfillment context, these
            // obligations could in principle be ignored: they have
            // already been registered when the cache entry was
            // created (and hence the new ones will quickly be
            // discarded as duplicated). But when doing trait
            // evaluation this is not the case, and dropping the trait
            // evaluations can causes ICEs (e.g. #43132).
            debug!("opt_normalize_projection_type: \
                    found normalized ty `{:?}`",
                   ty);
            return Some(ty);
        }
        Err(ProjectionCacheEntry::Error) => {
            debug!("opt_normalize_projection_type: \
                    found error");
            return Some(normalize_to_error(selcx, param_env, projection_ty, cause, depth));
        }
    }

    let obligation = Obligation::with_depth(cause.clone(), depth, param_env, projection_ty);
    match project_type(selcx, &obligation) {
        Ok(ProjectedTy::Progress(Progress { ty: projected_ty, mut obligations })) => {
            // if projection succeeded, then what we get out of this
            // is also non-normalized (consider: it was derived from
            // an impl, where-clause etc) and hence we must
            // re-normalize it

            debug!("opt_normalize_projection_type: \
                    projected_ty={:?} \
                    depth={} \
                    obligations={:?}",
                   projected_ty,
                   depth,
                   obligations);

            let result = if projected_ty.has_projections() {
                let mut normalizer = AssociatedTypeNormalizer::new(selcx,
                                                                   param_env,
                                                                   cause,
                                                                   depth+1);
                let normalized_ty = normalizer.fold(&projected_ty);

                debug!("opt_normalize_projection_type: \
                        normalized_ty={:?} depth={}",
                       normalized_ty,
                       depth);

                obligations.extend(normalizer.obligations);
                Normalized {
                    value: normalized_ty,
                    obligations,
                }
            } else {
                Normalized {
                    value: projected_ty,
                    obligations,
                }
            };
            infcx.projection_cache.borrow_mut().insert_ty(cache_key, &result);
            Some(result)
        }
        Ok(ProjectedTy::NoProgress(projected_ty)) => {
            debug!("opt_normalize_projection_type: \
                    projected_ty={:?} no progress",
                   projected_ty);
            let result = Normalized {
                value: projected_ty,
                obligations: vec![]
            };
            infcx.projection_cache.borrow_mut().insert_ty(cache_key, &result);
            Some(result)
        }
        Err(ProjectionTyError::TooManyCandidates) => {
            debug!("opt_normalize_projection_type: \
                    too many candidates");
            infcx.projection_cache.borrow_mut()
                                  .ambiguous(cache_key);
            None
        }
        Err(ProjectionTyError::TraitSelectionError(_)) => {
            debug!("opt_normalize_projection_type: ERROR");
            // if we got an error processing the `T as Trait` part,
            // just return `ty::err` but add the obligation `T :
            // Trait`, which when processed will cause the error to be
            // reported later

            infcx.projection_cache.borrow_mut()
                                  .error(cache_key);
            Some(normalize_to_error(selcx, param_env, projection_ty, cause, depth))
        }
    }
}

/// If we are projecting `<T as Trait>::Item`, but `T: Trait` does not
/// hold. In various error cases, we cannot generate a valid
/// normalized projection. Therefore, we create an inference variable
/// return an associated obligation that, when fulfilled, will lead to
/// an error.
///
/// Note that we used to return `TyError` here, but that was quite
/// dubious -- the premise was that an error would *eventually* be
/// reported, when the obligation was processed. But in general once
/// you see a `TyError` you are supposed to be able to assume that an
/// error *has been* reported, so that you can take whatever heuristic
/// paths you want to take. To make things worse, it was possible for
/// cycles to arise, where you basically had a setup like `<MyType<$0>
/// as Trait>::Foo == $0`. Here, normalizing `<MyType<$0> as
/// Trait>::Foo> to `[type error]` would lead to an obligation of
/// `<MyType<[type error]> as Trait>::Foo`.  We are supposed to report
/// an error for this obligation, but we legitimately should not,
/// because it contains `[type error]`. Yuck! (See issue #29857 for
/// one case where this arose.)
fn normalize_to_error<'a, 'gcx, 'tcx>(selcx: &mut SelectionContext<'a, 'gcx, 'tcx>,
                                      param_env: ty::ParamEnv<'tcx>,
                                      projection_ty: ty::ProjectionTy<'tcx>,
                                      cause: ObligationCause<'tcx>,
                                      depth: usize)
                                      -> NormalizedTy<'tcx>
{
    let trait_ref = projection_ty.trait_ref(selcx.tcx()).to_poly_trait_ref();
    let trait_obligation = Obligation { cause,
                                        recursion_depth: depth,
                                        param_env,
                                        predicate: trait_ref.to_predicate() };
    let tcx = selcx.infcx().tcx;
    let def_id = projection_ty.item_def_id;
    let new_value = selcx.infcx().next_ty_var(
        TypeVariableOrigin::NormalizeProjectionType(tcx.def_span(def_id)));
    Normalized {
        value: new_value,
        obligations: vec![trait_obligation]
    }
}

enum ProjectedTy<'tcx> {
    Progress(Progress<'tcx>),
    NoProgress(Ty<'tcx>),
}

struct Progress<'tcx> {
    ty: Ty<'tcx>,
    obligations: Vec<PredicateObligation<'tcx>>,
}

impl<'tcx> Progress<'tcx> {
    fn error<'a,'gcx>(tcx: TyCtxt<'a,'gcx,'tcx>) -> Self {
        Progress {
            ty: tcx.types.err,
            obligations: vec![],
        }
    }

    fn with_addl_obligations(mut self,
                             mut obligations: Vec<PredicateObligation<'tcx>>)
                             -> Self {
        debug!("with_addl_obligations: self.obligations.len={} obligations.len={}",
               self.obligations.len(), obligations.len());

        debug!("with_addl_obligations: self.obligations={:?} obligations={:?}",
               self.obligations, obligations);

        self.obligations.append(&mut obligations);
        self
    }
}

/// Compute the result of a projection type (if we can).
///
/// IMPORTANT:
/// - `obligation` must be fully normalized
fn project_type<'cx, 'gcx, 'tcx>(
    selcx: &mut SelectionContext<'cx, 'gcx, 'tcx>,
    obligation: &ProjectionTyObligation<'tcx>)
    -> Result<ProjectedTy<'tcx>, ProjectionTyError<'tcx>>
{
    debug!("project(obligation={:?})",
           obligation);

    let recursion_limit = selcx.tcx().sess.recursion_limit.get();
    if obligation.recursion_depth >= recursion_limit {
        debug!("project: overflow!");
        selcx.infcx().report_overflow_error(&obligation, true);
    }

    let obligation_trait_ref = &obligation.predicate.trait_ref(selcx.tcx());

    debug!("project: obligation_trait_ref={:?}", obligation_trait_ref);

    if obligation_trait_ref.references_error() {
        return Ok(ProjectedTy::Progress(Progress::error(selcx.tcx())));
    }

    let mut candidates = ProjectionTyCandidateSet {
        vec: Vec::new(),
        ambiguous: false,
    };

    assemble_candidates_from_param_env(selcx,
                                       obligation,
                                       &obligation_trait_ref,
                                       &mut candidates);

    assemble_candidates_from_trait_def(selcx,
                                       obligation,
                                       &obligation_trait_ref,
                                       &mut candidates);

    if let Err(e) = assemble_candidates_from_impls(selcx,
                                                   obligation,
                                                   &obligation_trait_ref,
                                                   &mut candidates) {
        return Err(ProjectionTyError::TraitSelectionError(e));
    }

    debug!("{} candidates, ambiguous={}",
           candidates.vec.len(),
           candidates.ambiguous);

    // Inherent ambiguity that prevents us from even enumerating the
    // candidates.
    if candidates.ambiguous {
        return Err(ProjectionTyError::TooManyCandidates);
    }

    // Drop duplicates.
    //
    // Note: `candidates.vec` seems to be on the critical path of the
    // compiler. Replacing it with an hash set was also tried, which would
    // render the following dedup unnecessary. It led to cleaner code but
    // prolonged compiling time of `librustc` from 5m30s to 6m in one test, or
    // ~9% performance lost.
    if candidates.vec.len() > 1 {
        let mut i = 0;
        while i < candidates.vec.len() {
            let has_dup = (0..i).any(|j| candidates.vec[i] == candidates.vec[j]);
            if has_dup {
                candidates.vec.swap_remove(i);
            } else {
                i += 1;
            }
        }
    }

    // Prefer where-clauses. As in select, if there are multiple
    // candidates, we prefer where-clause candidates over impls.  This
    // may seem a bit surprising, since impls are the source of
    // "truth" in some sense, but in fact some of the impls that SEEM
    // applicable are not, because of nested obligations. Where
    // clauses are the safer choice. See the comment on
    // `select::SelectionCandidate` and #21974 for more details.
    if candidates.vec.len() > 1 {
        debug!("retaining param-env candidates only from {:?}", candidates.vec);
        candidates.vec.retain(|c| match *c {
            ProjectionTyCandidate::ParamEnv(..) => true,
            ProjectionTyCandidate::TraitDef(..) |
            ProjectionTyCandidate::Select => false,
        });
        debug!("resulting candidate set: {:?}", candidates.vec);
        if candidates.vec.len() != 1 {
            return Err(ProjectionTyError::TooManyCandidates);
        }
    }

    assert!(candidates.vec.len() <= 1);

    match candidates.vec.pop() {
        Some(candidate) => {
            Ok(ProjectedTy::Progress(
                confirm_candidate(selcx,
                                  obligation,
                                  &obligation_trait_ref,
                                  candidate)))
        }
        None => Ok(ProjectedTy::NoProgress(
                    selcx.tcx().mk_projection(
                        obligation.predicate.item_def_id,
                        obligation.predicate.substs)))
    }
}

/// The first thing we have to do is scan through the parameter
/// environment to see whether there are any projection predicates
/// there that can answer this question.
fn assemble_candidates_from_param_env<'cx, 'gcx, 'tcx>(
    selcx: &mut SelectionContext<'cx, 'gcx, 'tcx>,
    obligation: &ProjectionTyObligation<'tcx>,
    obligation_trait_ref: &ty::TraitRef<'tcx>,
    candidate_set: &mut ProjectionTyCandidateSet<'tcx>)
{
    debug!("assemble_candidates_from_param_env(..)");
    assemble_candidates_from_predicates(selcx,
                                        obligation,
                                        obligation_trait_ref,
                                        candidate_set,
                                        ProjectionTyCandidate::ParamEnv,
                                        obligation.param_env.caller_bounds.iter().cloned());
}

/// In the case of a nested projection like <<A as Foo>::FooT as Bar>::BarT, we may find
/// that the definition of `Foo` has some clues:
///
/// ```
/// trait Foo {
///     type FooT : Bar<BarT=i32>
/// }
/// ```
///
/// Here, for example, we could conclude that the result is `i32`.
fn assemble_candidates_from_trait_def<'cx, 'gcx, 'tcx>(
    selcx: &mut SelectionContext<'cx, 'gcx, 'tcx>,
    obligation: &ProjectionTyObligation<'tcx>,
    obligation_trait_ref: &ty::TraitRef<'tcx>,
    candidate_set: &mut ProjectionTyCandidateSet<'tcx>)
{
    debug!("assemble_candidates_from_trait_def(..)");

    let tcx = selcx.tcx();
    // Check whether the self-type is itself a projection.
    let (def_id, substs) = match obligation_trait_ref.self_ty().sty {
        ty::TyProjection(ref data) => {
            (data.trait_ref(tcx).def_id, data.substs)
        }
        ty::TyAnon(def_id, substs) => (def_id, substs),
        ty::TyInfer(ty::TyVar(_)) => {
            // If the self-type is an inference variable, then it MAY wind up
            // being a projected type, so induce an ambiguity.
            candidate_set.ambiguous = true;
            return;
        }
        _ => { return; }
    };

    // If so, extract what we know from the trait and try to come up with a good answer.
    let trait_predicates = tcx.predicates_of(def_id);
    let bounds = trait_predicates.instantiate(tcx, substs);
    let bounds = elaborate_predicates(tcx, bounds.predicates);
    assemble_candidates_from_predicates(selcx,
                                        obligation,
                                        obligation_trait_ref,
                                        candidate_set,
                                        ProjectionTyCandidate::TraitDef,
                                        bounds)
}

fn assemble_candidates_from_predicates<'cx, 'gcx, 'tcx, I>(
    selcx: &mut SelectionContext<'cx, 'gcx, 'tcx>,
    obligation: &ProjectionTyObligation<'tcx>,
    obligation_trait_ref: &ty::TraitRef<'tcx>,
    candidate_set: &mut ProjectionTyCandidateSet<'tcx>,
    ctor: fn(ty::PolyProjectionPredicate<'tcx>) -> ProjectionTyCandidate<'tcx>,
    env_predicates: I)
    where I: IntoIterator<Item=ty::Predicate<'tcx>>
{
    debug!("assemble_candidates_from_predicates(obligation={:?})",
           obligation);
    let infcx = selcx.infcx();
    for predicate in env_predicates {
        debug!("assemble_candidates_from_predicates: predicate={:?}",
               predicate);
        match predicate {
            ty::Predicate::Projection(ref data) => {
                let same_def_id =
                    data.0.projection_ty.item_def_id == obligation.predicate.item_def_id;

                let is_match = same_def_id && infcx.probe(|_| {
                    let data_poly_trait_ref =
                        data.to_poly_trait_ref(infcx.tcx);
                    let obligation_poly_trait_ref =
                        obligation_trait_ref.to_poly_trait_ref();
                    infcx.at(&obligation.cause, obligation.param_env)
                         .sup(obligation_poly_trait_ref, data_poly_trait_ref)
                         .map(|InferOk { obligations: _, value: () }| {
                             // FIXME(#32730) -- do we need to take obligations
                             // into account in any way? At the moment, no.
                         })
                         .is_ok()
                });

                debug!("assemble_candidates_from_predicates: candidate={:?} \
                                                             is_match={} same_def_id={}",
                       data, is_match, same_def_id);

                if is_match {
                    candidate_set.vec.push(ctor(data.clone()));
                }
            }
            _ => { }
        }
    }
}

fn assemble_candidates_from_impls<'cx, 'gcx, 'tcx>(
    selcx: &mut SelectionContext<'cx, 'gcx, 'tcx>,
    obligation: &ProjectionTyObligation<'tcx>,
    obligation_trait_ref: &ty::TraitRef<'tcx>,
    candidate_set: &mut ProjectionTyCandidateSet<'tcx>)
    -> Result<(), SelectionError<'tcx>>
{
    // If we are resolving `<T as TraitRef<...>>::Item == Type`,
    // start out by selecting the predicate `T as TraitRef<...>`:
    let poly_trait_ref = obligation_trait_ref.to_poly_trait_ref();
    let trait_obligation = obligation.with(poly_trait_ref.to_poly_trait_predicate());
    selcx.infcx().probe(|_| {
        let vtable = match selcx.select(&trait_obligation) {
            Ok(Some(vtable)) => vtable,
            Ok(None) => {
                candidate_set.ambiguous = true;
                return Ok(());
            }
            Err(e) => {
                debug!("assemble_candidates_from_impls: selection error {:?}",
                       e);
                return Err(e);
            }
        };

        match vtable {
            super::VtableClosure(_) |
            super::VtableGenerator(_) |
            super::VtableFnPointer(_) |
            super::VtableObject(_) => {
                debug!("assemble_candidates_from_impls: vtable={:?}",
                       vtable);

                candidate_set.vec.push(ProjectionTyCandidate::Select);
            }
            super::VtableImpl(ref impl_data) => {
                // We have to be careful when projecting out of an
                // impl because of specialization. If we are not in
                // trans (i.e., projection mode is not "any"), and the
                // impl's type is declared as default, then we disable
                // projection (even if the trait ref is fully
                // monomorphic). In the case where trait ref is not
                // fully monomorphic (i.e., includes type parameters),
                // this is because those type parameters may
                // ultimately be bound to types from other crates that
                // may have specialized impls we can't see. In the
                // case where the trait ref IS fully monomorphic, this
                // is a policy decision that we made in the RFC in
                // order to preserve flexibility for the crate that
                // defined the specializable impl to specialize later
                // for existing types.
                //
                // In either case, we handle this by not adding a
                // candidate for an impl if it contains a `default`
                // type.
                let item_name = selcx.tcx().associated_item(obligation.predicate.item_def_id).name;
                let node_item = assoc_ty_def(selcx,
                                             impl_data.impl_def_id,
                                             item_name);

                let is_default = if node_item.node.is_from_trait() {
                    // If true, the impl inherited a `type Foo = Bar`
                    // given in the trait, which is implicitly default.
                    // Otherwise, the impl did not specify `type` and
                    // neither did the trait:
                    //
                    // ```rust
                    // trait Foo { type T; }
                    // impl Foo for Bar { }
                    // ```
                    //
                    // This is an error, but it will be
                    // reported in `check_impl_items_against_trait`.
                    // We accept it here but will flag it as
                    // an error when we confirm the candidate
                    // (which will ultimately lead to `normalize_to_error`
                    // being invoked).
                    node_item.item.defaultness.has_value()
                } else {
                    node_item.item.defaultness.is_default() ||
                    selcx.tcx().impl_is_default(node_item.node.def_id())
                };

                // Only reveal a specializable default if we're past type-checking
                // and the obligations is monomorphic, otherwise passes such as
                // transmute checking and polymorphic MIR optimizations could
                // get a result which isn't correct for all monomorphizations.
                let new_candidate = if !is_default {
                    Some(ProjectionTyCandidate::Select)
                } else if obligation.param_env.reveal == Reveal::All {
                    assert!(!poly_trait_ref.needs_infer());
                    if !poly_trait_ref.needs_subst() {
                        Some(ProjectionTyCandidate::Select)
                    } else {
                        None
                    }
                } else {
                    None
                };

                candidate_set.vec.extend(new_candidate);
            }
            super::VtableParam(..) => {
                // This case tell us nothing about the value of an
                // associated type. Consider:
                //
                // ```
                // trait SomeTrait { type Foo; }
                // fn foo<T:SomeTrait>(...) { }
                // ```
                //
                // If the user writes `<T as SomeTrait>::Foo`, then the `T
                // : SomeTrait` binding does not help us decide what the
                // type `Foo` is (at least, not more specifically than
                // what we already knew).
                //
                // But wait, you say! What about an example like this:
                //
                // ```
                // fn bar<T:SomeTrait<Foo=usize>>(...) { ... }
                // ```
                //
                // Doesn't the `T : Sometrait<Foo=usize>` predicate help
                // resolve `T::Foo`? And of course it does, but in fact
                // that single predicate is desugared into two predicates
                // in the compiler: a trait predicate (`T : SomeTrait`) and a
                // projection. And the projection where clause is handled
                // in `assemble_candidates_from_param_env`.
            }
            super::VtableDefaultImpl(..) |
            super::VtableBuiltin(..) => {
                // These traits have no associated types.
                span_bug!(
                    obligation.cause.span,
                    "Cannot project an associated type from `{:?}`",
                    vtable);
            }
        }

        Ok(())
    })
}

fn confirm_candidate<'cx, 'gcx, 'tcx>(
    selcx: &mut SelectionContext<'cx, 'gcx, 'tcx>,
    obligation: &ProjectionTyObligation<'tcx>,
    obligation_trait_ref: &ty::TraitRef<'tcx>,
    candidate: ProjectionTyCandidate<'tcx>)
    -> Progress<'tcx>
{
    debug!("confirm_candidate(candidate={:?}, obligation={:?})",
           candidate,
           obligation);

    match candidate {
        ProjectionTyCandidate::ParamEnv(poly_projection) |
        ProjectionTyCandidate::TraitDef(poly_projection) => {
            confirm_param_env_candidate(selcx, obligation, poly_projection)
        }

        ProjectionTyCandidate::Select => {
            confirm_select_candidate(selcx, obligation, obligation_trait_ref)
        }
    }
}

fn confirm_select_candidate<'cx, 'gcx, 'tcx>(
    selcx: &mut SelectionContext<'cx, 'gcx, 'tcx>,
    obligation: &ProjectionTyObligation<'tcx>,
    obligation_trait_ref: &ty::TraitRef<'tcx>)
    -> Progress<'tcx>
{
    let poly_trait_ref = obligation_trait_ref.to_poly_trait_ref();
    let trait_obligation = obligation.with(poly_trait_ref.to_poly_trait_predicate());
    let vtable = match selcx.select(&trait_obligation) {
        Ok(Some(vtable)) => vtable,
        _ => {
            span_bug!(
                obligation.cause.span,
                "Failed to select `{:?}`",
                trait_obligation);
        }
    };

    match vtable {
        super::VtableImpl(data) =>
            confirm_impl_candidate(selcx, obligation, data),
        super::VtableGenerator(data) =>
            confirm_generator_candidate(selcx, obligation, data),
        super::VtableClosure(data) =>
            confirm_closure_candidate(selcx, obligation, data),
        super::VtableFnPointer(data) =>
            confirm_fn_pointer_candidate(selcx, obligation, data),
        super::VtableObject(_) =>
            confirm_object_candidate(selcx, obligation, obligation_trait_ref),
        super::VtableDefaultImpl(..) |
        super::VtableParam(..) |
        super::VtableBuiltin(..) =>
            // we don't create Select candidates with this kind of resolution
            span_bug!(
                obligation.cause.span,
                "Cannot project an associated type from `{:?}`",
                vtable),
    }
}

fn confirm_object_candidate<'cx, 'gcx, 'tcx>(
    selcx: &mut SelectionContext<'cx, 'gcx, 'tcx>,
    obligation:  &ProjectionTyObligation<'tcx>,
    obligation_trait_ref: &ty::TraitRef<'tcx>)
    -> Progress<'tcx>
{
    let self_ty = obligation_trait_ref.self_ty();
    let object_ty = selcx.infcx().shallow_resolve(self_ty);
    debug!("confirm_object_candidate(object_ty={:?})",
           object_ty);
    let data = match object_ty.sty {
        ty::TyDynamic(ref data, ..) => data,
        _ => {
            span_bug!(
                obligation.cause.span,
                "confirm_object_candidate called with non-object: {:?}",
                object_ty)
        }
    };
    let env_predicates = data.projection_bounds().map(|p| {
        p.with_self_ty(selcx.tcx(), object_ty).to_predicate()
    }).collect();
    let env_predicate = {
        let env_predicates = elaborate_predicates(selcx.tcx(), env_predicates);

        // select only those projections that are actually projecting an
        // item with the correct name
        let env_predicates = env_predicates.filter_map(|p| match p {
            ty::Predicate::Projection(data) =>
                if data.0.projection_ty.item_def_id == obligation.predicate.item_def_id {
                    Some(data)
                } else {
                    None
                },
            _ => None
        });

        // select those with a relevant trait-ref
        let mut env_predicates = env_predicates.filter(|data| {
            let data_poly_trait_ref = data.to_poly_trait_ref(selcx.tcx());
            let obligation_poly_trait_ref = obligation_trait_ref.to_poly_trait_ref();
            selcx.infcx().probe(|_| {
                selcx.infcx().at(&obligation.cause, obligation.param_env)
                             .sup(obligation_poly_trait_ref, data_poly_trait_ref)
                             .is_ok()
            })
        });

        // select the first matching one; there really ought to be one or
        // else the object type is not WF, since an object type should
        // include all of its projections explicitly
        match env_predicates.next() {
            Some(env_predicate) => env_predicate,
            None => {
                debug!("confirm_object_candidate: no env-predicate \
                        found in object type `{:?}`; ill-formed",
                       object_ty);
                return Progress::error(selcx.tcx());
            }
        }
    };

    confirm_param_env_candidate(selcx, obligation, env_predicate)
}

fn confirm_generator_candidate<'cx, 'gcx, 'tcx>(
    selcx: &mut SelectionContext<'cx, 'gcx, 'tcx>,
    obligation: &ProjectionTyObligation<'tcx>,
    vtable: VtableGeneratorData<'tcx, PredicateObligation<'tcx>>)
    -> Progress<'tcx>
{
    let gen_sig = selcx.infcx().generator_sig(vtable.closure_def_id).unwrap()
        .subst(selcx.tcx(), vtable.substs.substs);
    let Normalized {
        value: gen_sig,
        obligations
    } = normalize_with_depth(selcx,
                             obligation.param_env,
                             obligation.cause.clone(),
                             obligation.recursion_depth+1,
                             &gen_sig);

    debug!("confirm_generator_candidate: obligation={:?},gen_sig={:?},obligations={:?}",
           obligation,
           gen_sig,
           obligations);

    let tcx = selcx.tcx();

    let gen_def_id = tcx.lang_items.gen_trait().unwrap();

    // Note: we unwrap the binder here but re-create it below (1)
    let ty::Binder((trait_ref, yield_ty, return_ty)) =
        tcx.generator_trait_ref_and_outputs(gen_def_id,
                                            obligation.predicate.self_ty(),
                                            gen_sig);

    let name = tcx.associated_item(obligation.predicate.item_def_id).name;
    let ty = if name == Symbol::intern("Return") {
        return_ty
    } else if name == Symbol::intern("Yield") {
        yield_ty
    } else {
        bug!()
    };

    let predicate = ty::Binder(ty::ProjectionPredicate { // (1) recreate binder here
        projection_ty: ty::ProjectionTy {
            substs: trait_ref.substs,
            item_def_id: obligation.predicate.item_def_id,
        },
        ty: ty
    });

    confirm_param_env_candidate(selcx, obligation, predicate)
        .with_addl_obligations(vtable.nested)
        .with_addl_obligations(obligations)
}

fn confirm_fn_pointer_candidate<'cx, 'gcx, 'tcx>(
    selcx: &mut SelectionContext<'cx, 'gcx, 'tcx>,
    obligation: &ProjectionTyObligation<'tcx>,
    fn_pointer_vtable: VtableFnPointerData<'tcx, PredicateObligation<'tcx>>)
    -> Progress<'tcx>
{
    let fn_type = selcx.infcx().shallow_resolve(fn_pointer_vtable.fn_ty);
    let sig = fn_type.fn_sig(selcx.tcx());
    let Normalized {
        value: sig,
        obligations
    } = normalize_with_depth(selcx,
                             obligation.param_env,
                             obligation.cause.clone(),
                             obligation.recursion_depth+1,
                             &sig);

    confirm_callable_candidate(selcx, obligation, sig, util::TupleArgumentsFlag::Yes)
        .with_addl_obligations(fn_pointer_vtable.nested)
        .with_addl_obligations(obligations)
}

fn confirm_closure_candidate<'cx, 'gcx, 'tcx>(
    selcx: &mut SelectionContext<'cx, 'gcx, 'tcx>,
    obligation: &ProjectionTyObligation<'tcx>,
    vtable: VtableClosureData<'tcx, PredicateObligation<'tcx>>)
    -> Progress<'tcx>
{
    let closure_typer = selcx.closure_typer();
    let closure_type = closure_typer.fn_sig(vtable.closure_def_id)
        .subst(selcx.tcx(), vtable.substs.substs);
    let Normalized {
        value: closure_type,
        obligations
    } = normalize_with_depth(selcx,
                             obligation.param_env,
                             obligation.cause.clone(),
                             obligation.recursion_depth+1,
                             &closure_type);

    debug!("confirm_closure_candidate: obligation={:?},closure_type={:?},obligations={:?}",
           obligation,
           closure_type,
           obligations);

    confirm_callable_candidate(selcx,
                               obligation,
                               closure_type,
                               util::TupleArgumentsFlag::No)
        .with_addl_obligations(vtable.nested)
        .with_addl_obligations(obligations)
}

fn confirm_callable_candidate<'cx, 'gcx, 'tcx>(
    selcx: &mut SelectionContext<'cx, 'gcx, 'tcx>,
    obligation: &ProjectionTyObligation<'tcx>,
    fn_sig: ty::PolyFnSig<'tcx>,
    flag: util::TupleArgumentsFlag)
    -> Progress<'tcx>
{
    let tcx = selcx.tcx();

    debug!("confirm_callable_candidate({:?},{:?})",
           obligation,
           fn_sig);

    // the `Output` associated type is declared on `FnOnce`
    let fn_once_def_id = tcx.lang_items.fn_once_trait().unwrap();

    // Note: we unwrap the binder here but re-create it below (1)
    let ty::Binder((trait_ref, ret_type)) =
        tcx.closure_trait_ref_and_return_type(fn_once_def_id,
                                              obligation.predicate.self_ty(),
                                              fn_sig,
                                              flag);

    let predicate = ty::Binder(ty::ProjectionPredicate { // (1) recreate binder here
        projection_ty: ty::ProjectionTy::from_ref_and_name(
            tcx,
            trait_ref,
            Symbol::intern(FN_OUTPUT_NAME),
        ),
        ty: ret_type
    });

    confirm_param_env_candidate(selcx, obligation, predicate)
}

fn confirm_param_env_candidate<'cx, 'gcx, 'tcx>(
    selcx: &mut SelectionContext<'cx, 'gcx, 'tcx>,
    obligation: &ProjectionTyObligation<'tcx>,
    poly_projection: ty::PolyProjectionPredicate<'tcx>)
    -> Progress<'tcx>
{
    let infcx = selcx.infcx();
    let cause = obligation.cause.clone();
    let param_env = obligation.param_env;
    let trait_ref = obligation.predicate.trait_ref(infcx.tcx);
    match infcx.match_poly_projection_predicate(cause, param_env, poly_projection, trait_ref) {
        Ok(InferOk { value: ty_match, obligations }) => {
            Progress {
                ty: ty_match.value,
                obligations,
            }
        }
        Err(e) => {
            span_bug!(
                obligation.cause.span,
                "Failed to unify obligation `{:?}` \
                 with poly_projection `{:?}`: {:?}",
                obligation,
                poly_projection,
                e);
        }
    }
}

fn confirm_impl_candidate<'cx, 'gcx, 'tcx>(
    selcx: &mut SelectionContext<'cx, 'gcx, 'tcx>,
    obligation: &ProjectionTyObligation<'tcx>,
    impl_vtable: VtableImplData<'tcx, PredicateObligation<'tcx>>)
    -> Progress<'tcx>
{
    let VtableImplData { substs, nested, impl_def_id } = impl_vtable;

    let tcx = selcx.tcx();
    let param_env = obligation.param_env;
    let assoc_ty = assoc_ty_def(selcx, impl_def_id,
        tcx.associated_item(obligation.predicate.item_def_id).name);

    let ty = if !assoc_ty.item.defaultness.has_value() {
        // This means that the impl is missing a definition for the
        // associated type. This error will be reported by the type
        // checker method `check_impl_items_against_trait`, so here we
        // just return TyError.
        debug!("confirm_impl_candidate: no associated type {:?} for {:?}",
               assoc_ty.item.name,
               obligation.predicate);
        tcx.types.err
    } else {
        tcx.type_of(assoc_ty.item.def_id)
    };
    let substs = translate_substs(selcx.infcx(), param_env, impl_def_id, substs, assoc_ty.node);
    Progress {
        ty: ty.subst(tcx, substs),
        obligations: nested,
    }
}

/// Locate the definition of an associated type in the specialization hierarchy,
/// starting from the given impl.
///
/// Based on the "projection mode", this lookup may in fact only examine the
/// topmost impl. See the comments for `Reveal` for more details.
fn assoc_ty_def<'cx, 'gcx, 'tcx>(
    selcx: &SelectionContext<'cx, 'gcx, 'tcx>,
    impl_def_id: DefId,
    assoc_ty_name: ast::Name)
    -> specialization_graph::NodeItem<ty::AssociatedItem>
{
    let tcx = selcx.tcx();
    let trait_def_id = tcx.impl_trait_ref(impl_def_id).unwrap().def_id;
    let trait_def = tcx.trait_def(trait_def_id);

    // This function may be called while we are still building the
    // specialization graph that is queried below (via TraidDef::ancestors()),
    // so, in order to avoid unnecessary infinite recursion, we manually look
    // for the associated item at the given impl.
    // If there is no such item in that impl, this function will fail with a
    // cycle error if the specialization graph is currently being built.
    let impl_node = specialization_graph::Node::Impl(impl_def_id);
    for item in impl_node.items(tcx) {
        if item.kind == ty::AssociatedKind::Type && item.name == assoc_ty_name {
            return specialization_graph::NodeItem {
                node: specialization_graph::Node::Impl(impl_def_id),
                item,
            };
        }
    }

    if let Some(assoc_item) = trait_def
        .ancestors(tcx, impl_def_id)
        .defs(tcx, assoc_ty_name, ty::AssociatedKind::Type)
        .next() {
        assoc_item
    } else {
        // This is saying that neither the trait nor
        // the impl contain a definition for this
        // associated type.  Normally this situation
        // could only arise through a compiler bug --
        // if the user wrote a bad item name, it
        // should have failed in astconv.
        bug!("No associated type `{}` for {}",
             assoc_ty_name,
             tcx.item_path_str(impl_def_id))
    }
}

// # Cache

/// The projection cache. Unlike the standard caches, this can
/// include infcx-dependent type variables - therefore, we have to roll
/// the cache back each time we roll a snapshot back, to avoid assumptions
/// on yet-unresolved inference variables. Types with skolemized regions
/// also have to be removed when the respective snapshot ends.
///
/// Because of that, projection cache entries can be "stranded" and left
/// inaccessible when type variables inside the key are resolved. We make no
/// attempt to recover or remove "stranded" entries, but rather let them be
/// (for the lifetime of the infcx).
///
/// Entries in the projection cache might contain inference variables
/// that will be resolved by obligations on the projection cache entry - e.g.
/// when a type parameter in the associated type is constrained through
/// an "RFC 447" projection on the impl.
///
/// When working with a fulfillment context, the derived obligations of each
/// projection cache entry will be registered on the fulfillcx, so any users
/// that can wait for a fulfillcx fixed point need not care about this. However,
/// users that don't wait for a fixed point (e.g. trait evaluation) have to
/// resolve the obligations themselves to make sure the projected result is
/// ok and avoid issues like #43132.
///
/// If that is done, after evaluation the obligations, it is a good idea to
/// call `ProjectionCache::complete` to make sure the obligations won't be
/// re-evaluated and avoid an exponential worst-case.
///
/// FIXME: we probably also want some sort of cross-infcx cache here to
/// reduce the amount of duplication. Let's see what we get with the Chalk
/// reforms.
pub struct ProjectionCache<'tcx> {
    map: SnapshotMap<ProjectionCacheKey<'tcx>, ProjectionCacheEntry<'tcx>>,
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct ProjectionCacheKey<'tcx> {
    ty: ty::ProjectionTy<'tcx>
}

impl<'cx, 'gcx, 'tcx> ProjectionCacheKey<'tcx> {
    pub fn from_poly_projection_predicate(selcx: &mut SelectionContext<'cx, 'gcx, 'tcx>,
                                          predicate: &ty::PolyProjectionPredicate<'tcx>)
                                          -> Option<Self>
    {
        let infcx = selcx.infcx();
        // We don't do cross-snapshot caching of obligations with escaping regions,
        // so there's no cache key to use
        infcx.tcx.no_late_bound_regions(&predicate)
            .map(|predicate| ProjectionCacheKey {
                // We don't attempt to match up with a specific type-variable state
                // from a specific call to `opt_normalize_projection_type` - if
                // there's no precise match, the original cache entry is "stranded"
                // anyway.
                ty: infcx.resolve_type_vars_if_possible(&predicate.projection_ty)
            })
    }
}

#[derive(Clone, Debug)]
enum ProjectionCacheEntry<'tcx> {
    InProgress,
    Ambiguous,
    Error,
    NormalizedTy(NormalizedTy<'tcx>),
}

// NB: intentionally not Clone
pub struct ProjectionCacheSnapshot {
    snapshot: Snapshot,
}

impl<'tcx> ProjectionCache<'tcx> {
    pub fn new() -> Self {
        ProjectionCache {
            map: SnapshotMap::new()
        }
    }

    pub fn snapshot(&mut self) -> ProjectionCacheSnapshot {
        ProjectionCacheSnapshot { snapshot: self.map.snapshot() }
    }

    pub fn rollback_to(&mut self, snapshot: ProjectionCacheSnapshot) {
        self.map.rollback_to(snapshot.snapshot);
    }

    pub fn rollback_skolemized(&mut self, snapshot: &ProjectionCacheSnapshot) {
        self.map.partial_rollback(&snapshot.snapshot, &|k| k.ty.has_re_skol());
    }

    pub fn commit(&mut self, snapshot: ProjectionCacheSnapshot) {
        self.map.commit(snapshot.snapshot);
    }

    /// Try to start normalize `key`; returns an error if
    /// normalization already occurred (this error corresponds to a
    /// cache hit, so it's actually a good thing).
    fn try_start(&mut self, key: ProjectionCacheKey<'tcx>)
                 -> Result<(), ProjectionCacheEntry<'tcx>> {
        if let Some(entry) = self.map.get(&key) {
            return Err(entry.clone());
        }

        self.map.insert(key, ProjectionCacheEntry::InProgress);
        Ok(())
    }

    /// Indicates that `key` was normalized to `value`.
    fn insert_ty(&mut self, key: ProjectionCacheKey<'tcx>, value: &NormalizedTy<'tcx>) {
        debug!("ProjectionCacheEntry::insert_ty: adding cache entry: key={:?}, value={:?}",
               key, value);
        let fresh_key = self.map.insert(key, ProjectionCacheEntry::NormalizedTy(value.clone()));
        assert!(!fresh_key, "never started projecting `{:?}`", key);
    }

    /// Mark the relevant projection cache key as having its derived obligations
    /// complete, so they won't have to be re-computed (this is OK to do in a
    /// snapshot - if the snapshot is rolled back, the obligations will be
    /// marked as incomplete again).
    pub fn complete(&mut self, key: ProjectionCacheKey<'tcx>) {
        let ty = match self.map.get(&key) {
            Some(&ProjectionCacheEntry::NormalizedTy(ref ty)) => {
                debug!("ProjectionCacheEntry::complete({:?}) - completing {:?}",
                       key, ty);
                ty.value
            }
            ref value => {
                // Type inference could "strand behind" old cache entries. Leave
                // them alone for now.
                debug!("ProjectionCacheEntry::complete({:?}) - ignoring {:?}",
                       key, value);
                return
            }
        };

        self.map.insert(key, ProjectionCacheEntry::NormalizedTy(Normalized {
            value: ty,
            obligations: vec![]
        }));
    }

    /// Indicates that trying to normalize `key` resulted in
    /// ambiguity. No point in trying it again then until we gain more
    /// type information (in which case, the "fully resolved" key will
    /// be different).
    fn ambiguous(&mut self, key: ProjectionCacheKey<'tcx>) {
        let fresh = self.map.insert(key, ProjectionCacheEntry::Ambiguous);
        assert!(!fresh, "never started projecting `{:?}`", key);
    }

    /// Indicates that trying to normalize `key` resulted in
    /// error.
    fn error(&mut self, key: ProjectionCacheKey<'tcx>) {
        let fresh = self.map.insert(key, ProjectionCacheEntry::Error);
        assert!(!fresh, "never started projecting `{:?}`", key);
    }
}
