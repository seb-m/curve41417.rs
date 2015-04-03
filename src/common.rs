//! Common
// FIXME: follow https://github.com/rust-lang/rust/pull/23549
#[allow(deprecated)]
use std::num::SignedInt;

use rand::os::OsRng;
use tars::allocator::Allocator;
use tars::ProtBuf8;


/// Size of Curve41417's scalar value
pub const SCALAR_SIZE: usize = 52;
/// Size of Curve41417's packed element
pub const BYTES_SIZE: usize = 52;


/// Trait to augment data buffers for scalar values
///
/// Provide required methods in order to use a data buffer as secret scalar
/// in Curve41417.
pub trait Scalar {
    /// Clamp its bytes to set its value in the range
    /// `8.{1,2,3,...,2^410-1} + 2^413`.
    fn clamp_41417(&mut self);
}

impl<A: Allocator> Scalar for ProtBuf8<A> {
    fn clamp_41417(&mut self) {
       clamp_buf(self);
    }
}

fn clamp_buf(b: &mut [u8]) {
    assert_eq!(b.len(), SCALAR_SIZE);
    b[51] = (b[51] & 63) | 32;
    b[0] = b[0] & 248;
}


/// `u64` to `bytes` little-endian encoding.
pub fn u64to8_le(buf: &mut [u8], val: &u64) {
    assert!(buf.len() >= 8);
    for i in 0_usize..8 {
        buf[i] = (*val >> (8 * i)) as u8;
    }
}

/// Conditionally swap bytes.
///
/// `x` and `y` are swapped iff `cond` is equal to `1`, there are left
/// unchanged iff `cond` is equal to `0`. Currently only works for arrays
/// of signed integers. `cond` is expected to be `0` or `1`.
// FIXME: follow https://github.com/rust-lang/rust/pull/23549
#[allow(deprecated)]
pub fn bytes_cswap<T: SignedInt>(cond: T, x: &mut [T], y: &mut [T]) {
    assert_eq!(x.len(), y.len());

    let c: T = !(cond - T::one());
    for i in 0_usize..x.len() {
        let t = c & (x[i] ^ y[i]);
        x[i] = x[i] ^ t;
        y[i] = y[i] ^ t;
    }
}

/// Instantiate a PRNG based on `OsRng` (on unixes it relies on
/// `/etc/[u]random`).
pub fn os_rng() -> OsRng {
    OsRng::new().unwrap()
}
