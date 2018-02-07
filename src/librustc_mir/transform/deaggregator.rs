// Copyright 2016 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use rustc::hir;
use rustc::ty::TyCtxt;
use rustc::mir::*;
use rustc_data_structures::indexed_vec::Idx;
use transform::{MirPass, MirSource};

pub struct Deaggregator;

impl MirPass for Deaggregator {
    fn run_pass<'a, 'tcx>(&self,
                          tcx: TyCtxt<'a, 'tcx, 'tcx>,
                          source: MirSource,
                          mir: &mut Mir<'tcx>) {
        // Don't run on constant MIR, because trans might not be able to
        // evaluate the modified MIR.
        // FIXME(eddyb) Remove check after miri is merged.
        let id = tcx.hir.as_local_node_id(source.def_id).unwrap();
        match (tcx.hir.body_owner_kind(id), source.promoted) {
            (_, Some(_)) |
            (hir::BodyOwnerKind::Const, _) |
            (hir::BodyOwnerKind::Static(_), _) => return,

            (hir::BodyOwnerKind::Fn, _) => {
                if tcx.is_const_fn(source.def_id) {
                    // Don't run on const functions, as, again, trans might not be able to evaluate
                    // the optimized IR.
                    return
                }
            }
        }

        // We only run when the MIR optimization level is > 2.
        if tcx.sess.opts.debugging_opts.mir_opt_level <= 2 {
            return;
        }

        for bb in mir.basic_blocks_mut() {
            let mut curr: usize = 0;
            while let Some(idx) = get_aggregate_statement_index(curr, &bb.statements) {
                // do the replacement
                debug!("removing statement {:?}", idx);
                let src_info = bb.statements[idx].source_info;
                let suffix_stmts = bb.statements.split_off(idx+1);
                let orig_stmt = bb.statements.pop().unwrap();
                let (lhs, rhs) = match orig_stmt.kind {
                    StatementKind::Assign(ref lhs, ref rhs) => (lhs, rhs),
                    _ => span_bug!(src_info.span, "expected assign, not {:?}", orig_stmt),
                };
                let (agg_kind, operands) = match rhs {
                    &Rvalue::Aggregate(ref agg_kind, ref operands) => (agg_kind, operands),
                    _ => span_bug!(src_info.span, "expected aggregate, not {:?}", rhs),
                };
                let (adt_def, variant, substs) = match **agg_kind {
                    AggregateKind::Adt(adt_def, variant, substs, None)
                        => (adt_def, variant, substs),
                    _ => span_bug!(src_info.span, "expected struct, not {:?}", rhs),
                };
                let n = bb.statements.len();
                bb.statements.reserve(n + operands.len() + suffix_stmts.len());
                for (i, op) in operands.iter().enumerate() {
                    let ref variant_def = adt_def.variants[variant];
                    let ty = variant_def.fields[i].ty(tcx, substs);
                    let rhs = Rvalue::Use(op.clone());

                    let lhs_cast = if adt_def.is_enum() {
                        Place::Projection(Box::new(PlaceProjection {
                            base: lhs.clone(),
                            elem: ProjectionElem::Downcast(adt_def, variant),
                        }))
                    } else {
                        lhs.clone()
                    };

                    let lhs_proj = Place::Projection(Box::new(PlaceProjection {
                        base: lhs_cast,
                        elem: ProjectionElem::Field(Field::new(i), ty),
                    }));
                    let new_statement = Statement {
                        source_info: src_info,
                        kind: StatementKind::Assign(lhs_proj, rhs),
                    };
                    debug!("inserting: {:?} @ {:?}", new_statement, idx + i);
                    bb.statements.push(new_statement);
                }

                // if the aggregate was an enum, we need to set the discriminant
                if adt_def.is_enum() {
                    let set_discriminant = Statement {
                        kind: StatementKind::SetDiscriminant {
                            place: lhs.clone(),
                            variant_index: variant,
                        },
                        source_info: src_info,
                    };
                    bb.statements.push(set_discriminant);
                };

                curr = bb.statements.len();
                bb.statements.extend(suffix_stmts);
            }
        }
    }
}

fn get_aggregate_statement_index<'a, 'tcx, 'b>(start: usize,
                                         statements: &Vec<Statement<'tcx>>)
                                         -> Option<usize> {
    for i in start..statements.len() {
        let ref statement = statements[i];
        let rhs = match statement.kind {
            StatementKind::Assign(_, ref rhs) => rhs,
            _ => continue,
        };
        let (kind, operands) = match rhs {
            &Rvalue::Aggregate(ref kind, ref operands) => (kind, operands),
            _ => continue,
        };
        let (adt_def, variant) = match **kind {
            AggregateKind::Adt(adt_def, variant, _, None) => (adt_def, variant),
            _ => continue,
        };
        if operands.len() == 0 {
            // don't deaggregate ()
            continue;
        }
        debug!("getting variant {:?}", variant);
        debug!("for adt_def {:?}", adt_def);
        return Some(i);
    };
    None
}
