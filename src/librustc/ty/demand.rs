// Copyright 2016 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use dep_graph::{DepNode, DepTrackingMap, DepTrackingMapConfig};
use hir::def_id::DefId;
use mir::Mir;
use ty::{self, TyCtxt, Ty};

use std::cell::RefCell;
use std::rc::Rc;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct Unsupported;

pub struct DepTrackingProvider<'tcx> {
    provider: Box<Provider<'tcx> + 'tcx>
}

impl<'tcx> DepTrackingProvider<'tcx> {
    pub fn new(provider: Box<Provider<'tcx> + 'tcx>) -> Self {
        DepTrackingProvider {
            provider: provider
        }
    }
}

pub struct Chain<A, B>(A, B);

fn dep_node_for_map<M: DepTrackingMapConfig>(_: &DepTrackingMap<M>, key: &M::Key)
                                             -> DepNode<DefId> {
    M::to_dep_node(key)
}

macro_rules! requests {
    (<$lt:tt> $($name:ident in $tcx:ident.$map:ident -> $ty:ty;)*) => {
        pub trait Provider<$lt> {
            $(fn $name<'a>(&self, _tcx: TyCtxt<'a, $lt, $lt>, _def_id: DefId)
                           -> Result<$ty, Unsupported> { Err(Unsupported) })*

            /// Produces a chained `Provider` that will use the second
            /// `Provider` to fulfill the request if this one can't.
            fn chain<T: Provider<$lt>>(self, second: T) -> Chain<Self, T> where Self: Sized {
                Chain(self, second)
            }
        }

        impl<$lt, A: Provider<$lt>, B: Provider<$lt>> Provider<$lt> for Chain<A, B> {
            $(fn $name<'a>(&self, tcx: TyCtxt<'a, $lt, $lt>, def_id: DefId)
                           -> Result<$ty, Unsupported> {
                match (self.0).$name(tcx, def_id) {
                    Err(Unsupported) => (self.1).$name(tcx, def_id),
                    response => response
                }
            })*
        }

        impl<$lt> Provider<$lt> for DepTrackingProvider<$lt> {
            $(#[inline]
            fn $name<'a>(&self, $tcx: TyCtxt<'a, $lt, $lt>, def_id: DefId)
                         -> Result<$ty, Unsupported> {
                let _task = {
                    let map = $tcx.$map.borrow();
                    if let Some(cached) = map.get(&def_id).cloned() {
                        return Ok(cached);
                    }
                    $tcx.dep_graph.in_task(dep_node_for_map(&map, &def_id))
                };

                self.provider.$name($tcx, def_id)
            })*
        }
    }
}

// Each of these requests is a method on a `Provider` trait
// and represents a piece of on-demand type-level information
// that can be obtained by calling it on `tcx.provider`.
// All `Provider` implementers must do their own cache stores
// into `tcx` maps (where applicable).
// The cache lookup fast-path and dep-graph tracking are
// automatic, as `tcx.provider` is a `DepTrackingProvider`
// wrapper around the actual chain of providers that the
// driver creates (using the various `rustc_*` crates).
requests! { <'tcx>
    ty in tcx.item_types -> Ty<'tcx>;
    generics in tcx.generics -> &'tcx ty::Generics<'tcx>;
    predicates in tcx.predicates -> Rc<ty::GenericPredicates<'tcx>>;
    super_predicates in tcx.super_predicates -> Rc<ty::GenericPredicates<'tcx>>;
    trait_def in tcx.trait_defs -> &'tcx ty::TraitDef;
    adt_def in tcx.adt_defs -> &'tcx ty::AdtDef;
    variances in tcx.item_variance_map -> Rc<Vec<ty::Variance>>;
    associated_item_def_ids in tcx.associated_item_def_ids -> Rc<Vec<DefId>>;
    associated_item in tcx.associated_items -> ty::AssociatedItem;
    impl_trait_ref in tcx.impl_trait_refs -> Option<ty::TraitRef<'tcx>>;
    custom_coerce_unsized_kind in tcx.custom_coerce_unsized_kinds
        -> ty::adjustment::CustomCoerceUnsized;
    mir in tcx.mir_map -> &'tcx RefCell<Mir<'tcx>>;
    closure_kind in tcx.closure_kinds -> ty::ClosureKind;
    closure_ty in tcx.closure_tys -> ty::ClosureTy<'tcx>;
}
