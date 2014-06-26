//! Raw bytes representations
//!
//! These containers are used to store packed scalars and curve points.
use serialize::hex::{FromHex, ToHex};
use std::fmt::{Show, Formatter, Result};
use std::from_str::FromStr;
use std::rand::{Rand, Rng};
use std::slice::bytes;

use ed::GroupElem;
use mont;
use sbuf::{DefaultAllocator, SBuf};
use utils;


/// Raw bytes-representation.
///
/// Used to pass data as input argument and for returning results in
/// crypto operations.
pub trait Bytes: PartialEq + Eq + Rand + Show + Clone + Collection {
    /// Return a new element with all its bytes set to zero.
    fn new_zero() -> Self;

    /// Return a new random element (use urandom as PRNG).
    fn new_rand() -> Self;

    /// Return a new instance from a byte slice.
    fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let mut nb: Self = Bytes::new_zero();

        if nb.len() != bytes.len() {
            return None;
        }

        bytes::copy_memory(nb.as_mut_bytes(), bytes);
        Some(nb)
    }

    /// Return a reference on the internal bytes as a byte slice.
    fn as_bytes<'a>(&'a self) -> &'a [u8];

    /// Return a mutable reference on the internal bytes as a mutable byte
    /// slice.
    fn as_mut_bytes<'a>(&'a mut self) -> &'a mut [u8];

    /// Return a reference to the byte at index `index`. Fails if
    /// `index` is out of bounds.
    fn get<'a>(&'a self, index: uint) -> &'a u8 {
        &self.as_bytes()[index]
    }

    /// Return a mutable reference to the byte at index `index`. Fails
    /// if `index` is out of bounds.
    fn get_mut<'a>(&'a mut self, index: uint) -> &'a mut u8 {
        &mut self.as_mut_bytes()[index]
    }
}


// These struct declarations are not inserted in the macro because
// it seems the macros variables cannot be expanded in the comments.
/// 52-bytes container.
#[deriving(Clone, Eq, PartialEq, Encodable, Decodable)]
pub struct B416 {
    bytes: SBuf<DefaultAllocator, u8>
}

impl B416 {
    /// Clamp its bytes to set its value in `8.{1,2,3,...,2^410-1} + 2^413`.
    pub fn clamp_41417(&mut self) {
        *self.get_mut(51) = (*self.get(51) & 63) | 32;
        *self.get_mut(0) = *self.get(0) & 248;
    }
}

/// 64-bytes container.
#[deriving(Clone, Eq, PartialEq, Encodable, Decodable)]
pub struct B512 {
    bytes: SBuf<DefaultAllocator, u8>
}

/// 104-bytes container.
#[deriving(Clone, Eq, PartialEq, Encodable, Decodable)]
pub struct B832 {
    bytes: SBuf<DefaultAllocator, u8>
}


macro_rules! bytes_impl(($name:ident, $test_mod_id:ident, $size:expr) => (

impl Bytes for $name {
    /// Return a new instance initialized to zero.
    fn new_zero() -> $name {
        $name {
            bytes: SBuf::<DefaultAllocator, u8>::new_zero($size)
        }
    }

    /// Return a new randomly generated instance (use urandom as PRNG).
    fn new_rand() -> $name {
        let rng = &mut utils::urandom_rng();
        Rand::rand(rng)
    }

    /// Return a reference on the internal bytes as a byte slice.
    fn as_bytes<'a>(&'a self) -> &'a [u8] {
        self.bytes.as_slice()
    }

    /// Return a mutable reference on the internal bytes as a mutable byte
    /// slice.
    fn as_mut_bytes<'a>(&'a mut self) -> &'a mut [u8] {
        self.bytes.as_mut_slice()
    }
}

impl FromStr for $name {
    /// Convert from an hex-string.
    fn from_str(s: &str) -> Option<$name> {
        let b = s.from_hex();
        if b.is_err() {
            return None
        }

        Bytes::from_bytes(b.unwrap().as_slice())
    }
}

impl Show for $name {
    /// Format as hex-string.
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "{}", self.to_hex())
    }
}

impl Rand for $name {
    /// Generate a new random instance. Be sure to use a secure
    /// PRNG when calling this method. For instance `Bytes::new_rand()`
    /// uses urandom.
    fn rand<R: Rng>(rng: &mut R) -> $name {
        let mut n: $name = Bytes::new_zero();
        rng.fill_bytes(n.as_mut_bytes());
        n
    }
}

impl Collection for $name {
    fn len(&self) -> uint {
        self.bytes.len()
    }
}

impl ToHex for $name {
    fn to_hex(&self) -> String {
        self.bytes.to_hex()
    }
}


#[cfg(test)]
mod $test_mod_id {
    use std::io::MemWriter;
    use std::rand::{Rng, Rand};
    use std::str;
    use std::from_str::FromStr;

    use bytes::{Bytes, $name};


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

    struct MockRng {
        val: u32
    }

    impl MockRng {
        pub fn new() -> MockRng {
            MockRng {
                val: 0x42424242
            }
        }
    }

    impl Rng for MockRng {
        fn next_u32(&mut self) -> u32 {
            self.val
        }
    }

    #[test]
    fn test_rand() {
        let mut rng = MockRng::new();
        let r: $name = Rand::rand(&mut rng);

        for i in range(0u, $size) {
            assert!(*r.get(i) == 0x42);
        }
    }
}

))

bytes_impl!(B416, test_b416, 52)
bytes_impl!(B512, test_b512, 64)
bytes_impl!(B832, test_b832, 104)


/// Tag `Bytes` containers deemed sufficiently large for providing a good
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
#[deriving(Clone, Show, Eq, PartialEq, Encodable, Decodable)]
pub struct $name(pub B416);

impl $name {
    /// Return the wrapped value as a reference.
    pub fn get_ref<'a>(&'a self) -> &'a B416 {
        let &$name(ref val) = self;
        val
    }

    /// Return a reference to the byte at index `index`. Fails if
    /// `index` is out of bounds.
    pub fn get<'a>(&'a self, index: uint) -> &'a u8 {
        self.get_ref().get(index)
    }

    /// Return the wrapped value, consume `self`.
    pub fn unwrap(self) -> B416 {
        let $name(val) = self;
        val
    }
}

impl ToHex for $name {
    fn to_hex(&self) -> String {
        self.get_ref().to_hex()
    }
}

))

wrapper_impl!(Scalar)
wrapper_impl!(MontPoint)
wrapper_impl!(EdPoint)


#[doc(hidden)]
trait ScalarMul<P> {
    fn mul(&self, lhs: &Scalar) -> P;
}

impl ScalarMul<MontPoint> for MontPoint {
    fn mul(&self, lhs: &Scalar) -> MontPoint {
        mont::scalar_mult(lhs, self)
    }
}

impl ScalarMul<EdPoint> for EdPoint {
    fn mul(&self, lhs: &Scalar) -> EdPoint {
        let p = GroupElem::unpack(self).unwrap();
        p.scalar_mult(lhs).pack()
    }
}

impl<S, R: ScalarMul<S>> Mul<R, S> for Scalar {
    /// Multiply scalar with point.
    fn mul(&self, other: &R) -> S {
        other.mul(self)
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

        let pke1 = sk * bpe;
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
