//! Raw bytes representations
//!
//! These containers are used to store packed scalars and curve points.
use serialize::{Encodable, Encoder, Decodable, Decoder};
use serialize::hex::{FromHex, ToHex};
use std::fmt;
use std::from_str::FromStr;
use std::io::Writer;
use std::rand::{Rand, Rng};
use std::slice::bytes;

use ed::GroupElem;
use mont;
use sbuf::{Allocator, DefaultAllocator, SBuf};
use utils;


/// Raw bytes-representation.
///
/// Used to pass data as input argument and for returning results in
/// crypto operations.
pub trait Bytes: PartialEq + Eq + Rand + fmt::Show + Clone + Collection +
    Index<uint, u8> + IndexMut<uint, u8> {
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
    fn as_bytes(&self) -> &[u8];

    /// Return a mutable reference on the internal bytes as a mutable byte
    /// slice.
    fn as_mut_bytes(&mut self) -> &mut [u8];

    /// Return a reference to the byte at index `index`. Fails if
    /// `index` is out of bounds.
    fn get(&self, index: uint) -> &u8 {
        &self.as_bytes()[index]
    }

    /// Return a mutable reference to the byte at index `index`. Fails
    /// if `index` is out of bounds.
    fn get_mut(&mut self, index: uint) -> &mut u8 {
        &mut self.as_mut_bytes()[index]
    }
}


// These struct declarations are not inserted in the macro because
// it seems the macros variables cannot be expanded in the comments.
/// 52-bytes container.
pub struct B416<A = DefaultAllocator> {
    bytes: SBuf<A, u8>
}

impl<A: Allocator> B416<A> {
    /// Clamp its bytes to set its value in `8.{1,2,3,...,2^410-1} + 2^413`.
    pub fn clamp_41417(&mut self) {
        (*self)[51] = ((*self)[51] & 63) | 32;
        (*self)[0] = (*self)[0] & 248;
    }
}

/// 64-bytes container.
pub struct B512<A = DefaultAllocator> {
    bytes: SBuf<A, u8>
}

/// 104-bytes container.
pub struct B832<A = DefaultAllocator> {
    bytes: SBuf<A, u8>
}


macro_rules! bytes_impl(($name:ident, $test_mod_id:ident, $size:expr) => (

impl<A: Allocator> $name<A> {
    /// Return the wrapped raw `SBuf` buffer value, consume `self`.
    pub fn unwrap(self) -> SBuf<A, u8> {
        self.bytes
    }

    /// Consume `buf` and transform it in Bxxx.
    pub fn from_sbuf(buf: SBuf<A, u8>) -> Option<$name<A>> {
        if buf.len() != $size {
            return None;
        }
        Some($name { bytes: buf })
    }
}

impl<A: Allocator> Bytes for $name<A> {
    /// Return a new instance initialized to zero.
    fn new_zero() -> $name<A> {
        $name {
            bytes: SBuf::<A, u8>::new_zero($size)
        }
    }

    /// Return a new randomly generated instance (use urandom as PRNG).
    fn new_rand() -> $name<A> {
        let rng = &mut utils::urandom_rng();
        Rand::rand(rng)
    }

    /// Return a reference on the internal bytes as a byte slice.
    fn as_bytes(&self) -> &[u8] {
        self.bytes.as_slice()
    }

    /// Return a mutable reference on the internal bytes as a mutable byte
    /// slice.
    fn as_mut_bytes(&mut self) -> &mut [u8] {
        self.bytes.as_mut_slice()
    }
}

impl<A: Allocator> Clone for $name<A> {
    fn clone(&self) -> $name<A> {
        $name {
            bytes: self.bytes.clone()
        }
    }
}

impl<A: Allocator> PartialEq for $name<A> {
    fn eq(&self, other: &$name<A>) -> bool {
        self.bytes == other.bytes
    }
}

impl<A: Allocator> Eq for $name<A> {
}

impl<A: Allocator, E, S: Encoder<E>> Encodable<S, E> for $name<A> {
    fn encode(&self, s: &mut S) -> Result<(), E> {
        self.bytes.encode(s)
    }
}

impl<A: Allocator, E, D: Decoder<E>> Decodable<D, E> for $name<A> {
    fn decode(d: &mut D) -> Result<$name<A>, E> {
        let s: SBuf<A, u8> = try!(Decodable::decode(d));
        if s.len() != $size {
            // Would prefer to return Err() here but the type may clash
            // with the type of the Decoder.
            fail!("Can't decode, invalid size.");
        }
        Ok($name {
            bytes: s
        })
    }
}

impl<A: Allocator> Index<uint, u8> for $name<A> {
    fn index(&self, index: &uint) -> &u8 {
        self.get(*index)
    }
}

impl<A: Allocator> IndexMut<uint, u8> for $name<A> {
    fn index_mut(&mut self, index: &uint) -> &mut u8 {
        self.get_mut(*index)
    }
}

impl<A: Allocator> FromStr for $name<A> {
    /// Convert from an hex-string.
    fn from_str(s: &str) -> Option<$name<A>> {
        let b = s.from_hex();
        if b.is_err() {
            return None
        }

        Bytes::from_bytes(b.unwrap().as_slice())
    }
}

impl<A: Allocator> fmt::Show for $name<A> {
    /// Format as hex-string.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_hex())
    }
}

impl<A: Allocator> Rand for $name<A> {
    /// Generate a new random instance. Be sure to use a secure
    /// PRNG when calling this method. For instance `Bytes::new_rand()`
    /// uses urandom.
    fn rand<R: Rng>(rng: &mut R) -> $name<A> {
        let mut n: $name<A> = Bytes::new_zero();
        rng.fill_bytes(n.as_mut_bytes());
        n
    }
}

impl<A: Allocator> Collection for $name<A> {
    fn len(&self) -> uint {
        self.bytes.len()
    }
}

impl<A: Allocator> ToHex for $name<A> {
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
    use sbuf::DefaultAllocator;


    #[test]
    fn test_basic() {
        let mut t: [u8, ..$size] = [0u8, ..$size];
        for i in range(0u, $size) {
            t[i] = i as u8;
        }
        let a: $name<DefaultAllocator> = Bytes::from_bytes(t).unwrap();
        let b: $name<DefaultAllocator> = Bytes::from_bytes(t).unwrap();
        let c: $name<DefaultAllocator> = Bytes::new_rand();

        assert!(a == b);
        assert!(a != c);

        let mut w = MemWriter::new();
        assert!(write!(&mut w, "{}", c).is_ok());
        let d: $name<DefaultAllocator> =
            FromStr::from_str(str::from_utf8(w.unwrap()
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
        let r: $name<DefaultAllocator> = Rand::rand(&mut rng);

        for i in range(0u, $size) {
            assert!(r[i] == 0x42);
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

impl<A: Allocator> Uniformity for B512<A> {
}

impl<A: Allocator> Uniformity for B832<A> {
}


macro_rules! wrapper_impl(($name:ident) => (

/// Wrapper around `B416` packed value used in crypto ops.
///
/// It is used to constrain input parameters and result values used
/// and returned in crypto operations in order to prevent wrong parameter
/// passing.
///
/// * `Scalar` wraps a scalar value
/// * `MontPoint` wraps a point in Montgomery's representation
/// * `EdPoint` wraps a point in Edwards representation
/// * `Elligator` wraps an indistinguishable Elligator byte-string
///
/// For instance you might create a new secret key like this:
///
/// ```
/// # extern crate curve41417;
/// # use curve41417::bytes::{B416, Bytes, Scalar, MontPoint};
/// # use curve41417::mont;
/// # fn main() {
/// let mut s: B416 = Bytes::new_rand();
/// s.clamp_41417();
/// let sk = Scalar(s);
/// let pk: MontPoint = mont::scalar_mult_base(&sk);
/// # }
/// ```
pub struct $name<A = DefaultAllocator>(pub B416<A>);

impl<A: Allocator> $name<A> {
    /// Return the wrapped value as a reference.
    pub fn get_ref(&self) -> &B416<A> {
        let &$name(ref val) = self;
        val
    }

    /// Return a reference to the byte at index `index`. Fails if
    /// `index` is out of bounds.
    pub fn get(&self, index: uint) -> &u8 {
        self.get_ref().get(index)
    }

    /// Return the wrapped value, consume `self`.
    pub fn unwrap(self) -> B416<A> {
        let $name(val) = self;
        val
    }
}

impl<A: Allocator> Clone for $name<A> {
    fn clone(&self) -> $name<A> {
        $name(self.get_ref().clone())
    }
}

impl<A: Allocator> PartialEq for $name<A> {
    fn eq(&self, other: &$name<A>) -> bool {
        self.get_ref() == other.get_ref()
    }
}

impl<A: Allocator> Eq for $name<A> {
}

impl<A: Allocator> fmt::Show for $name<A> {
    /// Format as hex-string.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.get_ref().fmt(f)
    }
}

impl<A: Allocator, E, S: Encoder<E>> Encodable<S, E> for $name<A> {
    fn encode(&self, s: &mut S) -> Result<(), E> {
        self.get_ref().encode(s)
    }
}

impl<A: Allocator, E, D: Decoder<E>> Decodable<D, E> for $name<A> {
    fn decode(d: &mut D) -> Result<$name<A>, E> {
        let b: B416<A> = try!(Decodable::decode(d));
        Ok($name(b))
    }
}

impl<A: Allocator> Index<uint, u8> for $name<A> {
    fn index(&self, index: &uint) -> &u8 {
        self.get(*index)
    }
}

impl<A: Allocator> ToHex for $name<A> {
    fn to_hex(&self) -> String {
        self.get_ref().to_hex()
    }
}

))

wrapper_impl!(Scalar)
wrapper_impl!(MontPoint)
wrapper_impl!(EdPoint)
wrapper_impl!(Elligator)


#[doc(hidden)]
trait ScalarMul<A, P> {
    fn mul(&self, lhs: &Scalar<A>) -> P;
}

impl<A: Allocator> ScalarMul<A, MontPoint<A>> for MontPoint<A> {
    fn mul(&self, lhs: &Scalar<A>) -> MontPoint<A> {
        mont::scalar_mult(lhs, self)
    }
}

impl<A: Allocator> ScalarMul<A, EdPoint<A>> for EdPoint<A> {
    fn mul(&self, lhs: &Scalar<A>) -> EdPoint<A> {
        let p = GroupElem::unpack(self).unwrap();
        p.scalar_mult(lhs).pack()
    }
}

impl<A: Allocator, S, R: ScalarMul<A, S>> Mul<R, S> for Scalar<A> {
    /// Multiply scalar with point.
    fn mul(&self, other: &R) -> S {
        other.mul(self)
    }
}

impl<A: Allocator> Mul<Scalar<A>, MontPoint<A>> for MontPoint<A> {
    /// Multiply point with scalar.
    fn mul(&self, other: &Scalar<A>) -> MontPoint<A> {
        mont::scalar_mult(other, self)
    }
}

impl<A: Allocator> Mul<Scalar<A>, EdPoint<A>> for EdPoint<A> {
    /// Multiply point with scalar.
    fn mul(&self, other: &Scalar<A>) -> EdPoint<A> {
        let p = GroupElem::unpack(self).unwrap();
        p.scalar_mult(other).pack()
    }
}


#[cfg(test)]
mod tests {
    use ed::GroupElem;
    use mont;
    use sbuf::DefaultAllocator;


    #[test]
    fn test_wrappers_basic() {
        let (pkm1, sk) = mont::keypair();
        let bpe = GroupElem::<DefaultAllocator>::base().pack();
        let bpm = GroupElem::<DefaultAllocator>::base().to_mont();

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
