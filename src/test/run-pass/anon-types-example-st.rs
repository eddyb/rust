// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

struct State;
type Error = ();

trait Bind<'a, F> {
    type Output: 'a;
    fn bind(self, f: F) -> Self::Output;
}

impl<'a, T, U, A: 'a, B, F: FnMut(T) -> B + 'a> Bind<'a, F> for A
where A: FnMut(&mut State) -> Result<T, Error>,
      B: FnMut(&mut State) -> Result<U, Error>
{
    type Output = impl FnMut(&mut State) -> Result<U, Error> + 'a;
    fn bind(mut self, mut f: F) -> Self::Output {
        move |state | {
            let r = try!(self(state));
            f(r)(state)
        }
    }
}

fn atom<'a, T: 'a>(x: T) -> impl FnMut(&mut State) -> Result<T, Error> + 'a {
    let mut x = Some(x);
    move |_| x.take().map_or(Err(()), Ok)
}

fn main() {
    assert_eq!(atom(5).bind(|x| atom(x > 4))(&mut State), Ok(true));
}
