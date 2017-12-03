// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![feature(advanced_slice_patterns)]
#![feature(box_patterns)]
#![feature(box_syntax)]
#![feature(slice_patterns)]

fn a() {
    let mut vec = [box 1, box 2, box 3];
    match vec {
        [box ref _a, _, _] => {
        //~^ immutable borrow occurs here
            vec[0] = box 4; //~ ERROR cannot borrow
            //~^ mutable borrow occurs here
        }
    } //~ immutable borrow ends here
}

fn b() {
    let mut vec = vec![box 1, box 2, box 3];
    let vec: &mut [Box<isize>] = &mut vec;
    match vec {
        &mut [ref _b..] => {
        //~^ immutable borrow occurs here
            vec[0] = box 4; //~ ERROR cannot borrow
            //~^ mutable borrow occurs here
        }
    } //~ immutable borrow ends here
}

fn c() {
    let mut vec = vec![box 1, box 2, box 3];
    let vec: &mut [Box<isize>] = &mut vec;
    match vec {
        &mut [_a, //~ ERROR cannot move out
            //~| cannot move out
            //~| to prevent move
            ..
        ] => {
            // Note: `_a` is *moved* here, but `b` is borrowing,
            // hence illegal.
            //
            // See comment in middle/borrowck/gather_loans/mod.rs
            // in the case covering these sorts of vectors.
        }
        _ => {}
    }
    let a = vec[0]; //~ ERROR cannot move out
    //~| cannot move out of indexed content
}

fn d() {
    let mut vec = vec![box 1, box 2, box 3];
    let vec: &mut [Box<isize>] = &mut vec;
    match vec {
        &mut [ //~ ERROR cannot move out
        //~^ cannot move out
         _b] => {} //~ NOTE to prevent move
        _ => {}
    }
    let a = vec[0]; //~ ERROR cannot move out
    //~| cannot move out of indexed content
}

fn e() {
    let mut vec = vec![box 1, box 2, box 3];
    let vec: &mut [Box<isize>] = &mut vec;
    match vec {
        &mut [_a, _b, _c] => {}  //~ ERROR cannot move out
        //~| cannot move out
        //~| NOTE to prevent move
        //~| NOTE and here
        //~| NOTE and here
        _ => {}
    }
    let a = vec[0]; //~ ERROR cannot move out
    //~| cannot move out of indexed content
}

fn main() {}
