//! Various checks
//!
//! # Note
//!
//! This API is completely unstable and subject to change.

#![doc(html_root_url = "https://doc.rust-lang.org/nightly/")]
#![feature(const_fn)]
#![feature(const_mut_refs)]
#![feature(in_band_lifetimes)]
#![feature(nll)]
#![feature(or_patterns)]
#![cfg_attr(bootstrap, feature(track_caller))]
#![recursion_limit = "256"]

#[macro_use]
extern crate rustc_middle;
#[macro_use]
extern crate log;

use rustc_middle::ty::query::Providers;

mod check_attr;
mod check_const;
pub mod dead;
mod diagnostic_items;
pub mod entry;
pub mod hir_id_validator;
pub mod hir_stats;
mod intrinsicck;
mod lang_items;
pub mod layout_test;
mod lib_features;
mod liveness;
pub mod loops;
mod reachable;
mod region;
pub mod stability;
mod upvars;
mod weak_lang_items;

pub const fn provide(providers: &mut Providers) {
    check_attr::provide(providers);
    check_const::provide(providers);
    diagnostic_items::provide(providers);
    entry::provide(providers);
    lang_items::provide(providers);
    lib_features::provide(providers);
    loops::provide(providers);
    liveness::provide(providers);
    intrinsicck::provide(providers);
    reachable::provide(providers);
    region::provide(providers);
    stability::provide(providers);
    upvars::provide(providers);
}
