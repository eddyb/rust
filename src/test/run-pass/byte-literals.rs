// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.
//
// ignore-lexer-test FIXME #15883


static FOO: u8 = b'\xF0';
static BAR: &'static [u8] = b"a\xF0\t";
static BAZ: &'static [u8] = br"a\n";

pub fn main() {
    assert_eq!(b'a', 97);
    assert_eq!(b'\n', 10);
    assert_eq!(b'\r', 13);
    assert_eq!(b'\t', 9);
    assert_eq!(b'\\', 92);
    assert_eq!(b'\'', 39);
    assert_eq!(b'\"', 34);
    assert_eq!(b'\0', 0);
    assert_eq!(b'\xF0', 240);
    assert_eq!(FOO, 240);

    match 42 {
        b'*' => {},
        _ => panic!()
    }

    match 100 {
        b'a' ... b'z' => {},
        _ => panic!()
    }

    let expected: &[_] = &[97, 10, 13, 9, 92, 39, 34, 0, 240];
    assert_eq!(b"a\n\r\t\\\'\"\0\xF0", expected);
    let expected: &[_] = &[97, 98];
    assert_eq!(b"a\
                 b", expected);
    let expected: &[_] = &[97, 240, 9];
    assert_eq!(BAR, expected);

    let val: &[_] = &[97, 10];
    match val {
        b"a\n" => {},
        _ => panic!(),
    }

    let buf = vec!(97, 98, 99, 100);
    assert_eq!(match &buf[0..3] {
         b"def" => 1,
         b"abc" => 2,
         _ => 3
    }, 2);

    let expected: &[_] = &[97, 92, 110];
    assert_eq!(BAZ, expected);
    let expected: &[_] = &[97, 92, 110];
    assert_eq!(br"a\n", expected);
    assert_eq!(br"a\n", b"a\\n");
    let expected: &[_] = &[97, 34, 35, 35, 98];
    assert_eq!(br###"a"##b"###, expected);
    assert_eq!(br###"a"##b"###, b"a\"##b");
}
