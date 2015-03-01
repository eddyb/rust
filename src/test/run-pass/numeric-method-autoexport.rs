// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// no-pretty-expanded

// This file is intended to test only that methods are automatically
// reachable for each numeric type, for each exported impl, with no imports
// necessary. Testing the methods of the impls is done within the source
// file for each numeric type.

use std::ops::Add;
use std::num::ToPrimitive;

pub fn main() {
// ints
    // num
    assert_eq!(15.add(6), 21);
    assert_eq!(15.add(6), 21);
    assert_eq!(15.add(6), 21);
    assert_eq!(15.add(6), 21);
    assert_eq!(15.add(6), 21);

// uints
    // num
    assert_eq!(15.add(6), 21);
    assert_eq!(15.add(6), 21);
    assert_eq!(15.add(6), 21);
    assert_eq!(15.add(6), 21);
    assert_eq!(15.add(6), 21);

// floats
    // num
    assert_eq!(10_f32.to_i32().unwrap(), 10);
    assert_eq!(10_f64.to_i32().unwrap(), 10);
}
