// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Test paths to associated types using the type-parameter-only sugar.

use std::ops::Deref;

pub trait Foo {
    type A;
    fn boo(&self) -> Self::A;
}

impl Foo for isize {
    type A = usize;
    fn boo(&self) -> usize {
        5
    }
}

// Using a type via a function.
pub fn bar<T: Foo>(a: T, x: T::A) -> T::A {
    let _: T::A = a.boo();
    x
}

// Using a type via an impl.
trait C {
    fn f();
    fn g(&self) { }
}
struct B<X>(X);
impl<T: Foo> C for B<T> {
    fn f() {
        let x: T::A = panic!();
    }
}

// Several layers of associated types, in both directions.
// FIXME(eddyb) This is pretty bad for larger testcases,
// the algorithm is currently `O((n * (n+1) / 2)!)`, with
// n = 4 here, that is, factorial of the number of HIR
// `<T>::Assoc` nodes, which is the sum 1 + 2 + ... + n.
// The reverse order *happens* to be faster though.
fn deref4_to_string_forward<T>(x: T) -> String
    where T: Deref,
          T::Target: Deref,
          T::Target::Target: Deref,
          T::Target::Target::Target: Deref,
          T::Target::Target::Target::Target: ToString
{
    x.to_string()
}

fn deref4_to_string_reverse<T>(x: T) -> String
    where T::Target::Target::Target::Target: ToString,
          T::Target::Target::Target: Deref,
          T::Target::Target: Deref,
          T::Target: Deref,
          T: Deref
{
    x.to_string()
}

pub fn main() {
    let z: usize = bar(2, 4);

    assert_eq!(deref4_to_string_forward(&&&&5), String::from("5"));
    assert_eq!(deref4_to_string_reverse(&&&&7), String::from("7"));
}
