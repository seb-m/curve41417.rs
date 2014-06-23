//! Secure Buffer.
use alloc::heap;
use libc::EINVAL;
use libc::funcs::bsd44;
use libc::funcs::posix88::mman;
use libc::types::common::c95::c_void;
use libc::types::os::arch::c95::{c_int, size_t};
use serialize::{Encodable, Encoder, Decodable, Decoder};
use serialize::hex::ToHex;
use std::fmt;
use std::intrinsics;
use std::mem;
use std::os;
use std::ptr;
use std::rand::Rng;
use std::raw::Slice;
use std::slice::{Items, MutItems};

use utils;


pub trait Allocator {
    fn new() -> Self;

    unsafe fn allocate(&self, size: uint, align: uint) -> *mut u8;

    unsafe fn deallocate(&self, ptr: *mut u8, size: uint, align: uint);
}

pub struct StdHeapAllocator;

impl Allocator for StdHeapAllocator {
    fn new() -> StdHeapAllocator {
        StdHeapAllocator
    }

    unsafe fn allocate(&self, size: uint, align: uint) -> *mut u8 {
        heap::allocate(size, align)
    }

    unsafe fn deallocate(&self, ptr: *mut u8, size: uint, align: uint) {
        heap::deallocate(ptr, size, align)
    }
}


unsafe fn alloc<A: Allocator, T>(count: uint) -> *mut T {
    let size_of_t = mem::size_of::<T>();

    assert!(size_of_t != 0 && count != 0);

    let size = count.checked_mul(&size_of_t)
                    .expect("alloc length overflow");

    // allocate
    let allocator: A = Allocator::new();
    let ptr = allocator.allocate(size, mem::min_align_of::<T>()) as *mut T;

    // mlock
    let ret = mman::mlock(ptr as *c_void, size as size_t);
    if ret != 0 {
        let errno = os::errno();
        fail!("mlock failed {} ({})",
              os::error_string(errno as uint), errno);
    }

    // madvise
    if cfg!(target_os = "linux") || cfg!(target_os = "android") {
        let dont_dump: c_int = 16;
        let ret = bsd44::madvise(ptr as *mut c_void, size as size_t, dont_dump);
        if ret != 0 {
            let errno = os::errno();
            // FIXME: EINVAL errors are currently ignored because on
            // Linux < 3.4 MADV_DONTDUMP is not a valid advice. There
            // should be a better way to check for the availability of
            // this flag in the kernel and in the libc.
            if errno != EINVAL as int {
                fail!("madvise failed {} ({})",
                      os::error_string(errno as uint), errno);
            }
        }
    }

    ptr
}

unsafe fn dealloc<A: Allocator, T>(ptr: *mut T, count: uint) {
    let size_of_t = mem::size_of::<T>();

    assert!(!ptr.is_null());
    assert!(size_of_t != 0);
    assert!(count != 0);

    let size = count.checked_mul(&size_of_t)
                    .expect("alloc length overflow");

    // zero-out
    // FIXME: not sure how much this llvm intrinsics could not be
    // optimized-out, maybe it would be better to use memset_s.
    intrinsics::volatile_set_memory(ptr, 0, count);

    // munlock
    let ret = mman::munlock(ptr as *c_void, size as size_t);
    if ret != 0 {
        let errno = os::errno();
        fail!("munlock failed {} ({})",
              os::error_string(errno as uint), errno);
    }

    // deallocate
    let allocator: A = Allocator::new();
    allocator.deallocate(ptr as *mut u8, size, mem::min_align_of::<T>())
}


pub struct SBuf<A, T> {
    len: uint,
    ptr: *mut T
}

impl<A: Allocator, T> SBuf<A, T> {
    fn from_raw_parts(length: uint, ptr: *mut T) -> SBuf<A, T> {
        SBuf {
            len: length,
            ptr: ptr
        }
    }

    fn size(&self) -> uint {
        self.len * mem::size_of::<T>()
    }

    fn with_length(length: uint) -> SBuf<A, T> {
        if mem::size_of::<T>() == 0 || length == 0 {
            return SBuf::from_raw_parts(0, 0 as *mut T);
        }

        let ptr = unsafe {
            alloc::<A, T>(length)
        };
        SBuf::from_raw_parts(length, ptr)
    }

    /// New allocated buffer with its memory zeroed-out.
    #[allow(experimental)]
    pub fn new_zero(length: uint) -> SBuf<A, T> {
        let n = SBuf::with_length(length);
        unsafe {
            ptr::zero_memory(n.ptr, length);
        }
        n
    }

    /// New allocated buffer with its memory randomly generated.
    pub fn new_rand(length: uint) -> SBuf<A, T> {
        let mut n = SBuf::with_length(length);
        let rng = &mut utils::urandom_rng();
        rng.fill_bytes(unsafe {
            mem::transmute(Slice {
                data: n.as_mut_ptr() as *u8,
                len: n.size()
            })
        });
        n
    }

    /// New buffer from slice.
    pub fn from_slice(values: &[T]) -> SBuf<A, T> {
        unsafe {
            SBuf::from_buf(values.as_ptr(), values.len())
        }
    }

    /// New buffer from unsafe buffer.
    pub unsafe fn from_buf(buf: *T, length: uint) -> SBuf<A, T> {
        assert!(!buf.is_null());
        let n = SBuf::with_length(length);
        ptr::copy_nonoverlapping_memory(n.ptr, buf, n.len);
        n
    }

    /// Return a pointer to buffer's memory.
    pub fn as_ptr(&self) -> *T {
        // (seb) Comment copied from vec.rs:
        // If we have a 0-sized vector, then the base pointer should not be NULL
        // because an iterator over the slice will attempt to yield the base
        // pointer as the first element in the vector, but this will end up
        // being Some(NULL) which is optimized to None.
        if mem::size_of::<T>() == 0 {
            1 as *T
        } else {
            self.ptr as *T
        }
    }

    /// Return a mutable pointer to buffer's memory.
    pub fn as_mut_ptr(&mut self) -> *mut T {
        // see above for the 0-size check
        if mem::size_of::<T>() == 0 {
            1 as *mut T
        } else {
            self.ptr
        }
    }

    /// Work with `self` as a slice.
    pub fn as_slice<'a>(&'a self) -> &'a [T] {
        unsafe {
            mem::transmute(Slice {
                data: self.as_ptr(),
                len: self.len
            })
        }
    }

    /// Work with `self` as a mutable slice.
    pub fn as_mut_slice<'a>(&'a mut self) -> &'a mut [T] {
        unsafe {
            mem::transmute(Slice {
                data: self.as_mut_ptr() as *T,
                len: self.len
            })
        }
    }

    /// Return a reference to the value at index `index`. Fails if
    /// `index` is out of bounds.
    pub fn get<'a>(&'a self, index: uint) -> &'a T {
        &self.as_slice()[index]
    }

    /// Return a mutable reference to the value at index `index`. Fails
    /// if `index` is out of bounds.
    pub fn get_mut<'a>(&'a mut self, index: uint) -> &'a mut T {
        &mut self.as_mut_slice()[index]
    }

    /// Return an iterator over references to the elements of the buffer
    /// in order.
    pub fn iter<'a>(&'a self) -> Items<'a, T> {
        self.as_slice().iter()
    }

    /// Return an iterator over mutable references to the elements of the
    /// buffer in order.
    pub fn mut_iter<'a>(&'a mut self) -> MutItems<'a, T> {
        self.as_mut_slice().mut_iter()
    }

    /// Return a slice of self spanning the interval [`start`, `end`).
    /// Fails when the slice (or part of it) is outside the bounds of self,
    /// or when `start` > `end`.
    pub fn slice<'a>(&'a self, start: uint, end: uint) -> &'a [T] {
        self.as_slice().slice(start, end)
    }

    /// Return a mutable slice of `self` between `start` and `end`.
    /// Fails when `start` or `end` point outside the bounds of `self`, or when
    /// `start` > `end`.
    pub fn mut_slice<'a>(&'a mut self, start: uint, end: uint) -> &'a mut [T] {
        self.as_mut_slice().mut_slice(start, end)
    }

    /// Return a slice of `self` from `start` to the end of the buffer.
    /// Fails when `start` points outside the bounds of self.
    pub fn slice_from<'a>(&'a self, start: uint) -> &'a [T] {
        self.as_slice().slice_from(start)
    }

    /// Return a mutable slice of self from `start` to the end of the buffer.
    /// Fails when `start` points outside the bounds of self.
    pub fn mut_slice_from<'a>(&'a mut self, start: uint) -> &'a mut [T] {
        self.as_mut_slice().mut_slice_from(start)
    }

    /// Return a slice of self from the start of the buffer to `end`.
    /// Fails when `end` points outside the bounds of self.
    pub fn slice_to<'a>(&'a self, end: uint) -> &'a [T] {
        self.as_slice().slice_to(end)
    }

    /// Return a mutable slice of self from the start of the buffer to `end`.
    /// Fails when `end` points outside the bounds of self.
    pub fn mut_slice_to<'a>(&'a mut self, end: uint) -> &'a mut [T] {
        self.as_mut_slice().mut_slice_to(end)
    }

    /// Return a pair of mutable slices that divides the buffer at an index.
    ///
    /// The first will contain all indices from `[0, mid)` (excluding the
    /// index `mid` itself) and the second will contain all indices from
    /// `[mid, len)` (excluding the index `len` itself). Fails if
    /// `mid > len`.
    pub fn mut_split_at<'a>(&'a mut self, mid: uint) -> (&'a mut [T],
                                                         &'a mut [T]) {
        self.as_mut_slice().mut_split_at(mid)
    }

    /// Reverse the order of elements in a buffer, in place.
    pub fn reverse(&mut self) {
        self.as_mut_slice().reverse()
    }
}

#[allow(dead_code)]
impl<A: Allocator, T: FromPrimitive> SBuf<A, T> {
    /// New buffer from bytes.
    fn from_bytes(bytes: &[u8]) -> SBuf<A, T> {
        let len = bytes.len();
        let mut n: SBuf<A, T> = SBuf::with_length(len);

        for i in range(0u, len) {
            *n.get_mut(i) = FromPrimitive::from_u8(bytes[i]).unwrap();
        }
        n
    }
}

#[unsafe_destructor]
impl<A: Allocator, T> Drop for SBuf<A, T> {
    fn drop(&mut self) {
        if self.len != 0 && !self.ptr.is_null() {
            unsafe {
                dealloc::<A, T>(self.ptr, self.len)
            }
        }
    }
}

impl<A: Allocator, T> Clone for SBuf<A, T> {
    fn clone(&self) -> SBuf<A, T> {
        SBuf::from_slice(self.as_slice())
    }
}

impl<A: Allocator, T> PartialEq for SBuf<A, T> {
    fn eq(&self, other: &SBuf<A, T>) -> bool {
        utils::bytes_eq(self.as_slice(), other.as_slice())
    }
}

impl<A: Allocator, T> Eq for SBuf<A, T> {
}

impl<A: Allocator, T> Collection for SBuf<A, T> {
    fn len(&self) -> uint {
        self.len
    }
}

impl<A: Allocator, T: fmt::Show> fmt::Show for SBuf<A, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.as_slice().fmt(f)
    }
}

impl<A: Allocator,
     E,
     S: Encoder<E>,
     T: Encodable<S, E>> Encodable<S, E> for SBuf<A, T> {
    fn encode(&self, s: &mut S) -> Result<(), E> {
        self.as_slice().encode(s)
    }
}

impl<A: Allocator,
     E,
     D: Decoder<E>,
     T: Decodable<D, E>> Decodable<D, E> for SBuf<A, T> {
    fn decode(d: &mut D) -> Result<SBuf<A, T>, E> {
        d.read_seq(|d, len| {
            let mut n = SBuf::with_length(len);
            for i in range(0, len) {
                *n.get_mut(i) = try!(d.read_seq_elt(i, |d| Decodable::decode(d)));
            }
            Ok(n)
        })
    }
}

impl<A: Allocator> ToHex for SBuf<A, u8> {
    fn to_hex(&self) -> String {
        let s = self.as_slice();
        s.to_hex()
    }
}

// FIXME: clean-up.
/*
impl<A: Allocator, T: ToHex> ToHex for SBuf<A, T> {
    fn to_hex(&self) -> String {
        let s = self.as_slice();
        s.to_hex()
       // let v: Vec<String> = self.iter().map(|e| e.to_hex()).collect();
       // v.concat()
    }
}

impl<A: Allocator, T: ToHex> ToHex for SBuf<A, T> {
    fn to_hex(&self) -> String {
        let v: Vec<String> = self.iter().map(|e| e.to_hex()).collect();
        v.concat()
    }
}

impl ToHex for u8 {
    fn to_hex(&self) -> String {
        self.to_str_radix(16)
    }
}
*/


#[cfg(test)]
mod test {
    use sbuf::{StdHeapAllocator, SBuf};


    #[test]
    fn test_basic() {
        let mut r: [i64, ..256] = [0, ..256];
        let mut s: [u8, ..256] = [0, ..256];

        let a: SBuf<StdHeapAllocator, i64> = SBuf::new_zero(256);
        assert!(a.as_slice() == r);

        for i in range(0u, 256) {
            r[i] = i as i64;
            s[i] = i as u8;
        }

        let b: SBuf<StdHeapAllocator, i64> = SBuf::from_bytes(s.as_slice());
        assert!(b.as_slice() == r);

        let c: SBuf<StdHeapAllocator, i64> = SBuf::from_slice(r.as_slice());
        assert!(c.as_slice() == r);

        let d: SBuf<StdHeapAllocator, i64> = unsafe {
            SBuf::from_buf(c.as_ptr(), c.len())
        };
        assert!(d == c);
    }
}
