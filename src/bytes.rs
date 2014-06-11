//! Raw bytes representations
//!
//! These containers are used to store packed scalars and curve points.
use std::default::Default;
use std::fmt::{Show, Formatter, Result};
use std::from_str::FromStr;
use std::num::FromStrRadix;
use std::rand::{Rand, Rng};
use std::slice::bytes;

use ed::GroupElem;
use mont;
use utils;
use utils::ZeroMemory;


/// Raw bytes-representation.
///
/// Used to pass data as input argument and for returning results in
/// crypto operations.
pub trait Bytes: PartialEq + Eq + Index<uint, u8> + Rand + Show +
    FromStr + Drop + Clone {
    /// Return a new element with all its bytes set to zero.
    fn new_zero() -> Self;

    /// Return a new random element (use urandom as PRNG).
    fn new_rand() -> Self;

    /// Instanciate a new `B416` object from a byte slice.
    fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let mut nb: Self = Bytes::new_zero();

        if nb.as_bytes().len() != bytes.len() {
            return None;
        }

        bytes::copy_memory(nb.as_mut_bytes(), bytes);
        Some(nb)
    }

    /// Access internal bytes as a byte slice.
    fn as_bytes<'a>(&'a self) -> &'a [u8];

    /// Access internal mutable bytes as a mutable byte slice.
    fn as_mut_bytes<'a>(&'a mut self) -> &'a mut [u8];

    /// Transform bytes to hex-string.
    fn to_str_hex(&self) -> String {
        utils::bytes_to_str_hex(self.as_bytes())
    }

    #[doc(hidden)]
    fn cleanup(&mut self) {
        self.as_mut_bytes().zero_memory();
    }
}


// These struct declarations are not inserted in the macro because
// it seems the macros variables cannot be expanded in the comments.
/// 52-bytes container.
pub struct B416 {
    bytes: [u8, ..52]
}

impl B416 {
    /// Clamp bytes to set value in `8.{1,2,3,...,2^410-1} + 2^413`.
    pub fn clamp_41417(&mut self) {
        self.bytes[51] = (self.bytes[51] & 63) | 32;
        self.bytes[0] &= 248;
    }
}

/// 64-bytes container.
pub struct B512 {
    bytes: [u8, ..64]
}

/// 104-bytes container.
pub struct B832 {
    bytes: [u8, ..104]
}


macro_rules! bytes_impl(($name:ident, $test_mod_id:ident, $size:expr) => (

impl Bytes for $name {
    /// Return a new instance initialized to zero.
    fn new_zero() -> $name {
        $name {
            bytes: [0u8, ..$size]
        }
    }

    /// Return a new randomly generated instance (use urandom as PRNG).
    fn new_rand() -> $name {
        let rng = &mut utils::urandom_rng();
        Rand::rand(rng)
    }

    /// Access internal bytes as a byte slice.
    fn as_bytes<'a>(&'a self) -> &'a [u8] {
        self.bytes.as_slice()
    }

    /// Access internal mutable bytes as a mutable byte slice.
    fn as_mut_bytes<'a>(&'a mut self) -> &'a mut [u8] {
        self.bytes.as_mut_slice()
    }
}

impl Drop for $name {
    /// Before being released the internal buffer is zeroed-out.
    fn drop(&mut self) {
        self.cleanup();
    }
}

impl Clone for $name {
    fn clone(&self) -> $name {
        Bytes::from_bytes(self.bytes).unwrap()
    }
}

impl Default for $name {
    /// Return a new random value (use urandom as PRNG).
    fn default() -> $name {
        Bytes::new_rand()
    }
}

impl FromStr for $name {
    /// Convert from an hex-string.
    fn from_str(s: &str) -> Option<$name> {
        if s.len() != $size * 2 {
            return None;
        }

        let mut b = [0u8, ..$size];
        for i in range(0u, $size) {
            b[i] = FromStrRadix::from_str_radix(String::from_str(s).as_slice().
                                                slice(2 * i, (i + 1) * 2),
                                                16).unwrap();
        }
        let r = Bytes::from_bytes(b);
        b.zero_memory();
        r
    }
}

impl Show for $name {
    /// Format as hex-string.
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "{}", self.to_str_hex())
    }
}

impl PartialEq for $name {
    /// Constant-time equality comparison.
    fn eq(&self, other: &$name) -> bool {
        utils::bytes_eq(self.bytes, other.bytes)
    }
}

impl Eq for $name {
}

impl Rand for $name {
    /// Generate a new random instance. Be sure to use a secure
    /// PRNG when calling this method. For instance `Bytes::new_rand()`
    /// uses urandom.
    fn rand<R: Rng>(rng: &mut R) -> $name {
        let mut n: $name = Bytes::new_zero();
        rng.fill_bytes(n.bytes);
        n
    }
}

impl Index<uint, u8> for $name {
    /// Return byte at `index`.
    fn index(&self, index: &uint) -> u8 {
        self.bytes.as_slice()[*index]
    }
}


#[cfg(test)]
mod $test_mod_id {
    use std::io::MemWriter;
    use std::str;
    use std::from_str::FromStr;

    use super::*;
    use bytes::Bytes;


    #[test]
    fn test_basic() {
        let mut t: [u8, ..$size] = [0u8, ..$size];
        for i in range(0u, $size) {
            t[i] = i as u8;
        }
        let a: $name = Bytes::from_bytes(t).unwrap();
        let b: $name = Bytes::from_bytes(t).unwrap();
        let c: $name = Bytes::new_rand();

        assert!(a == b);
        assert!(a != c);

        let mut w = MemWriter::new();
        assert!(write!(&mut w, "{}", c).is_ok());
        let d: $name = FromStr::from_str(str::from_utf8(w.unwrap()
                                                        .as_slice())
                                         .unwrap()).unwrap();
        assert!(d == c);

        let e = d.clone();
        assert!(d == e);
    }
}

))

bytes_impl!(B416, test_b416, 52)
bytes_impl!(B512, test_b512, 64)
bytes_impl!(B832, test_b832, 104)


/// Tag `Bytes` containers sufficiently large for providing a good
/// uniformity of the distribution `mod L`.
pub trait Uniformity {
}

impl Uniformity for B512 {
}

impl Uniformity for B832 {
}


macro_rules! wrapper_impl(($name:ident) => (

/// Wrapper around `B416` packed value used in crypto ops.
///
/// It is used to constrain input parameters and result values used
/// and returned in crypto operations in order to prevent wrong parameter
/// passing.
///
/// * `Scalar` denotes a wrapped scalar
/// * `MontPoint` denotes a wrapped point in Montgomery's representation
/// * `EdPoint` denotes a wrapped point in Edwards representation
///
/// For instance you might create a new secret key like this:
///
/// ```
/// use curve41417::bytes::{B416, Bytes, Scalar, MontPoint};
/// use curve41417::mont;
///
/// let mut s: B416 = Bytes::new_rand();
/// s.clamp_41417();
/// let sk = Scalar(s);
/// let pk: MontPoint = mont::scalar_mult_base(&sk);
/// ```
pub struct $name(pub B416);

impl $name {
    /// Access the wrapped value as a reference.
    pub fn get_ref<'a>(&'a self) -> &'a B416 {
        let &$name(ref val) = self;
        val
    }

    /// Return the wrapped value, consume `self`.
    pub fn unwrap(self) -> B416 {
        let $name(val) = self;
        val
    }
}

impl Clone for $name {
    fn clone(&self) -> $name {
        $name(self.get_ref().clone())
    }
}

impl Show for $name {
    /// Format the wrapped value as hex-string.
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "{}", self.get_ref().to_str_hex())
    }
}

impl PartialEq for $name {
    /// Compare wrapped values in constant time.
    fn eq(&self, other: &$name) -> bool {
        self.get_ref() == other.get_ref()
    }
}

impl Index<uint, u8> for $name {
    /// Return the byte at `index` in the wrapped value.
    fn index(&self, index: &uint) -> u8 {
        self.get_ref().as_bytes()[*index]
    }
}

))

wrapper_impl!(Scalar)
wrapper_impl!(MontPoint)
wrapper_impl!(EdPoint)


impl Mul<MontPoint, MontPoint> for Scalar {
    /// Multiply scalar with point.
    fn mul(&self, other: &MontPoint) -> MontPoint {
        mont::scalar_mult(self, other)
    }
}

impl Mul<Scalar, MontPoint> for MontPoint {
    /// Multiply point with scalar.
    fn mul(&self, other: &Scalar) -> MontPoint {
        mont::scalar_mult(other, self)
    }
}

impl Mul<Scalar, EdPoint> for EdPoint {
    /// Multiply point with scalar.
    fn mul(&self, other: &Scalar) -> EdPoint {
        let p = GroupElem::unpack(self).unwrap();
        p.scalar_mult(other).pack()
    }
}


#[cfg(test)]
mod tests {
    use ed::GroupElem;
    use mont;


    #[test]
    fn test_wrappers_basic() {
        let (pkm1, sk) = mont::keypair();
        let bpe = GroupElem::base().pack();
        let bpm = GroupElem::base().to_mont();

        let pkm2 = sk * bpm;
        assert!(pkm1 == pkm2);
        assert!(pkm1 == bpm * sk);

        let pke1 = bpe * sk;
        let pke2 = GroupElem::base().scalar_mult(&sk);
        let pke3 = pke2.pack();
        assert!(pke1 == pke3);

        let pkm3 = pke2.to_mont();
        assert!(pkm2 == pkm3);

        let sk2 = sk.clone();
        assert!(sk2 == sk);
        assert!(sk2.get_ref() == sk.get_ref());
    }
}
