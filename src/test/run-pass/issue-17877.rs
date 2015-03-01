// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

fn main() {
    assert_eq!(match [0; 1024] {
        _ => 42,
    }, 42);

    assert_eq!(match [0; 1024] {
        [1, _..] => 0,
        [0, _..] => 1,
        _ => 2
    }, 1);
}
