// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// revisions: ast mir
//[mir]compile-flags: -Z borrowck=mir

#![feature(slice_patterns)]

fn main() {
    let mut a = [1, 2, 3, 4];
    let t = match a {
        [1, 2, ref tail..] => tail,
        _ => unreachable!()
    };
    println!("t[0]: {}", t[0]);
    a[2] = 0;
    //[ast]~^ ERROR cannot borrow `a` as mutable because `a[..]` is also borrowed as immutable
    //[mir]~^^ ERROR cannot borrow `a` as mutable because it is also borrowed as immutable
    println!("t[0]: {}", t[0]);
    t[0];
}
