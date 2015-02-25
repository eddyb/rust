// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use prelude::v1::*;

use cell::UnsafeCell;
use sys::sync as ffi;

pub struct RWLock { inner: UnsafeCell<ffi::SRWLOCK> }

#[cfg(stage0)] // SNAP 522d09d
pub const RWLOCK_INIT: RWLock = RWLock {
    inner: UnsafeCell { value: ffi::SRWLOCK_INIT }
};

#[cfg(not(stage0))] // SNAP 522d09d
pub const RWLOCK_INIT: RWLock = RWLock {
    inner: UnsafeCell::new(ffi::SRWLOCK_INIT)
};

unsafe impl Send for RWLock {}
unsafe impl Sync for RWLock {}

impl RWLock {
    #[inline]
    pub unsafe fn read(&self) {
        ffi::AcquireSRWLockShared(self.inner.get())
    }
    #[inline]
    pub unsafe fn try_read(&self) -> bool {
        ffi::TryAcquireSRWLockShared(self.inner.get()) != 0
    }
    #[inline]
    pub unsafe fn write(&self) {
        ffi::AcquireSRWLockExclusive(self.inner.get())
    }
    #[inline]
    pub unsafe fn try_write(&self) -> bool {
        ffi::TryAcquireSRWLockExclusive(self.inner.get()) != 0
    }
    #[inline]
    pub unsafe fn read_unlock(&self) {
        ffi::ReleaseSRWLockShared(self.inner.get())
    }
    #[inline]
    pub unsafe fn write_unlock(&self) {
        ffi::ReleaseSRWLockExclusive(self.inner.get())
    }

    #[inline]
    pub unsafe fn destroy(&self) {
        // ...
    }
}
