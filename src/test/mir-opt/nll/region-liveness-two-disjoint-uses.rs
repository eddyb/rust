// Copyright 2012-2016 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Test for the subregion constraints. In this case, the region R3 on
// `p` includes two disjoint regions of the control-flow graph. The
// borrows in `&v[0]` and `&v[1]` each (in theory) have to outlive R3,
// but only at a particular point, and hence they wind up including
// distinct regions.

// compile-flags:-Znll -Zverbose
//                     ^^^^^^^^^ force compiler to dump more region information

#![allow(warnings)]

fn use_x(_: usize) -> bool { true }

fn main() {
    let mut v = [1, 2, 3];
    let mut p = &v[0];
    if true {
        use_x(*p);
    } else {
        use_x(22);
    }

    p = &v[1];
    use_x(*p);
}

// END RUST SOURCE
// START rustc.main.nll.0.mir
// | '_#2r: {bb1[1], bb2[0], bb2[1]}
// ...
// | '_#5r: {bb7[2], bb7[3], bb7[4], bb7[5]}
// | '_#6r: {bb1[1], bb2[0], bb2[1], bb7[2], bb7[3], bb7[4], bb7[5]}
// ...
// let mut _2: &'_#6r usize;
// ...
// _2 = &'_#2r (*_3)[_4];
// ...
// _2 = &'_#5r (*_11);
// END rustc.main.nll.0.mir
