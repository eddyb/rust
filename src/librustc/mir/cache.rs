// Copyright 2016 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use rustc_data_structures::indexed_vec::IndexVec;
use rustc_data_structures::sync::{RwLock, MappedReadGuard, ReadGuard};
use rustc_data_structures::stable_hasher::{HashStable, StableHasher,
                                           StableHasherResult};
use ich::StableHashingContext;
use mir::{Mir, BasicBlock};

use rustc_serialize;

#[derive(Clone, Debug)]
pub struct Cache {
    predecessors: RwLock<Option<IndexVec<BasicBlock, Vec<BasicBlock>>>>
}


impl rustc_serialize::Encodable for Cache {
    fn encode<S: rustc_serialize::Encoder>(&self, s: &mut S) -> Result<(), S::Error> {
        rustc_serialize::Encodable::encode(&(), s)
    }
}

impl rustc_serialize::Decodable for Cache {
    fn decode<D: rustc_serialize::Decoder>(d: &mut D) -> Result<Self, D::Error> {
        rustc_serialize::Decodable::decode(d).map(|_v: ()| Self::new())
    }
}

impl<'a> HashStable<StableHashingContext<'a>> for Cache {
    fn hash_stable<W: StableHasherResult>(&self,
                                          _: &mut StableHashingContext<'a>,
                                          _: &mut StableHasher<W>) {
        // do nothing
    }
}

impl Cache {
    pub fn new() -> Self {
        Cache {
            predecessors: RwLock::new(None)
        }
    }

    pub fn invalidate(&self) {
        // FIXME: consider being more fine-grained
        *self.predecessors.borrow_mut() = None;
    }

    pub fn predecessors(
        &self,
        mir: &Mir<'_>
    ) -> MappedReadGuard<'_, IndexVec<BasicBlock, Vec<BasicBlock>>> {
        if self.predecessors.borrow().is_none() {
            *self.predecessors.borrow_mut() = Some(calculate_predecessors(mir));
        }

        ReadGuard::map(self.predecessors.borrow(), |p| p.as_ref().unwrap())
    }
}

fn calculate_predecessors(mir: &Mir<'_>) -> IndexVec<BasicBlock, Vec<BasicBlock>> {
    let mut result = IndexVec::from_elem(vec![], mir.basic_blocks());
    for (bb, data) in mir.basic_blocks().iter_enumerated() {
        if let Some(ref term) = data.terminator {
            for &tgt in term.successors() {
                result[tgt].push(bb);
            }
        }
    }

    result
}

CloneTypeFoldableAndLiftImpls! {
    Cache,
}
