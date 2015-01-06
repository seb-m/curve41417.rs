//! Curve41417 scalar operations
use std::default::Default;
use std::fmt::{Show, Formatter, Result};
use std::num::FromPrimitive;
use std::ops::{Add, Sub, Neg, Mul, Index, IndexMut};
use std::rand::{Rand, Rng};

use tars::{ProtBuf, ProtBuf8};

use common::{self, BYTES_SIZE};


const SCE_SIZE: uint = 52;

// L is the prime order of the base point.
// L = 2^411 - d
//   = 2^411 - 33364140863755142520810177694098385178984727200411208589594759
const L: [u8; 52] = [
  0x79, 0xaf, 0x06, 0xe1, 0xa5, 0x71, 0x0e, 0x1b,
  0x18, 0xcf, 0x63, 0xad, 0x38, 0x03, 0x1c, 0x6f,
  0xb3, 0x22, 0x60, 0x70, 0xcf, 0x14, 0x24, 0xc9,
  0x3c, 0xeb, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
  0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
  0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
  0xff, 0xff, 0xff, 0x07
];

// LD = 2^5 * d
const LD: [u8; 27] = [
  0xe0, 0x10, 0x2a, 0xdf, 0x43, 0xcb, 0x31, 0x9e,
  0xfc, 0x1c, 0x86, 0x53, 0xea, 0x98, 0x7f, 0x1c,
  0x92, 0xa9, 0xfb, 0xf3, 0x11, 0x66, 0x7d, 0xdb,
  0x66, 0x98, 0x02
];


/// Scalar element used in scalar operations.
///
/// Provide commons Curve41417 scalar operations computed `mod L`, where
/// `L` is the prime order of the base point `ed::base()` currently used.
pub struct ScalarElem {
    elem: ProtBuf<i64>
}

impl ScalarElem {
    // Return a new scalar element with its value set to `0`.
    fn new_zero() -> ScalarElem {
        ScalarElem::zero()
    }

    /// Generate a new random `ScalarElem` between `[0, L-1]`.
    /// Use `OsRng` (which uses `/dev/[u]random` on Unix) as PRNG.
    pub fn new_rand() -> ScalarElem {
        let rng = &mut common::os_rng();
        Rand::rand(rng)
    }

    /// Return scalar value representing zero.
    pub fn zero() -> ScalarElem {
        ScalarElem {
            elem: ProtBuf::new_zero(SCE_SIZE)
        }
    }

    // Return a reference to the limb at index `index`; otherwise
    // return `None` if `index` is out of bounds.
    #[doc(hidden)]
    pub fn get(&self, index: uint) -> Option<&i64> {
        self.elem.get(index)
    }

    // Return a mutable reference to the limb at index `index`; otherwise
    // return `None` if `index` is out of bounds.
    #[doc(hidden)]
    pub fn get_mut(&mut self, index: uint) -> Option<&mut i64> {
        self.elem.get_mut(index)
    }

    pub fn len(&self) -> uint {
        self.elem.len()
    }

    // Conditionally swap this scalar element with `other`. `cond` serves
    // as condition and must be `0` or `1` strictly. Values are swapped iff
    // `cond == 1`.
    fn cswap(&mut self, cond: i64, other: &mut ScalarElem) {
        common::bytes_cswap::<i64>(cond,
                                   self.elem.as_mut_slice(),
                                   other.elem.as_mut_slice());
    }

    // Requirements: len >= 52
    fn carry(&mut self) {
        let top = self.len() - 1;
        let mut carry: i64;

        for i in range(0u, top) {
            self[i] += 1_i64 << 8;
            carry = self[i] >> 8;
            self[i + 1] += carry - 1;
            self[i] -= carry << 8;
        }

        self[top] += 1_i64 << 8;
        carry = self[top] >> 8;
        for i in range(0u, 27) {
            self[top - 51 + i] += (carry - 1) * (LD[i] as i64);
        }
        self[top] -= carry << 8;
    }

    // Reduce mod 2^416 - 2^5 * d and put limbs between [0, 2^16-1] through
    // carry.
    // Requirements: 52 < nlen <= 104
    fn reduce_weak(&mut self, n: &[i64]) {
        assert!(n.len() > 52);
        assert!(n.len() <= 104);

        let mut t: ProtBuf<i64> = ProtBuf::new_zero(78);
        for i in range(0u, 52) {
            t[i] = n[i];
        }

        for i in range(52u, n.len()) {
            for j in range(0u, 27) {
                t[i + j - 52] += n[i] * (LD[j] as i64);
            }
        }

        for i in range(52u, n.len() - 26) {
            for j in range(0u, 27) {
                t[i + j - 52] += t[i] * (LD[j] as i64);
            }
        }

        for i in range(0u, 52) {
            self[i] = t[i];
        }

        self.carry();
        self.carry();
    }

    fn reduce(&mut self) {
        self.carry();
        self.carry();

        // Eliminate multiples of 2^411
        let mut carry: i64 = 0;
        for i in range(0u, 52) {
            self[i] += carry - (self[51] >> 3) * (L[i] as i64);
            carry = self[i] >> 8;
            self[i] &= 0xff;
        }

        // Substract L a last time in case n is in [L, 2^411-1]
        let mut m = ScalarElem::new_zero();
        carry = 0;
        for i in range(0u, 52) {
            m[i] = self[i] + carry - (L[i] as i64);
            carry = m[i] >> 8;
            m[i] &= 0xff;
        }
        self.cswap(1 - (carry & 1), &mut m);
    }

    fn unpack_wo_reduce(n: &[u8]) -> ScalarElem {
        // Note: would be great to also check/assert that n is in [0, L - 1].
        let mut r = ScalarElem::new_zero();

        for i in range(0u, 52) {
            r[i] = n[i] as i64;
        }
        r
    }

    fn unpack_w_reduce(n: &[u8]) -> ScalarElem {
        let mut t: ProtBuf<i64> = ProtBuf::new_zero(n.len());

        for i in range(0u, n.len()) {
            t[i] = n[i] as i64;
        }

        let mut r = ScalarElem::new_zero();
        r.reduce_weak(t[]);
        r
    }

    /// Pack the current scalar value reduced `mod L`. Note: it is not
    /// until this method is called that the scalar element is reduced to
    /// its canonical form.
    pub fn pack(&self) -> ProtBuf8 {
        let mut t = self.clone();
        t.reduce();

        let mut b = ProtBuf::new_zero(BYTES_SIZE);
        for i in range(0u, BYTES_SIZE) {
            b[i] = (t[i] & 0xff) as u8;
        }
        b
    }

    /// Check if `self` is equal to `0`.
    pub fn is_zero(&self) -> bool {
        *self == ScalarElem::zero()
    }
}

impl<T: AsSlice<u8>> ScalarElem {
    /// Unpack scalar value `n`. It must represent a value strictly in
    /// `[0, L-1]` and it should not be expected to be reduced on unpacking.
    pub fn unpack(n: &T) -> Option<ScalarElem> {
        let nb = n.as_slice();
        match nb.len() {
            BYTES_SIZE => Some(ScalarElem::unpack_wo_reduce(nb)),
            _ => None
        }
    }

    /// Unpack bytes `b` as a scalar and reduce it `mod L`. It is expected
    /// to be of a large enough size in order to provide a good uniformity
    /// of distribution on reductions `mod L`. Thus `b` must be between
    /// `[64, 104]` bytes.
    pub fn unpack_from_bytes(b: &T) -> Option<ScalarElem> {
        let nb = b.as_slice();
        match nb.len() {
            64...104 => Some(ScalarElem::unpack_w_reduce(nb)),
            _ => None
        }
    }

    /// Unpack bytes `b` as a scalar, reduce it `mod L` and return the
    /// packed reduced result. See `unpack_from_bytes()` for more details
    /// on performed unpacking.
    pub fn reduce_from_bytes(b: &T) -> ProtBuf8 {
        ScalarElem::unpack_from_bytes(b).unwrap().pack()
    }
}

impl Clone for ScalarElem {
    fn clone(&self) -> ScalarElem {
        ScalarElem {
            elem: self.elem.clone()
        }
    }
}

impl Index<uint> for ScalarElem {
    type Output = i64;

    fn index(&self, index: &uint) -> &i64 {
        &self.elem[*index]
    }
}

impl IndexMut<uint> for ScalarElem {
    type Output = i64;

    fn index_mut(&mut self, index: &uint) -> &mut i64 {
        &mut self.elem[*index]
    }
}

impl<'a, 'b> Add<&'a ScalarElem> for &'b ScalarElem {
    type Output = ScalarElem;

    /// Add scalars.
    fn add(self, other: &ScalarElem) -> ScalarElem {
        let mut r = self.clone();
        for i in range(0u, self.len()) {
            r[i] += other[i];
        }
        r
    }
}

impl<'a, 'b> Sub<&'a ScalarElem> for &'b ScalarElem {
    type Output = ScalarElem;

    /// Substract scalars.
    fn sub(self, other: &ScalarElem) -> ScalarElem {
        let mut r = self.clone();
        for i in range(0u, self.len()) {
            r[i] -= other[i];
        }
        r
    }
}

impl<'a> Neg for &'a ScalarElem {
    type Output = ScalarElem;

    /// Negate scalar.
    fn neg(self) -> ScalarElem {
        &ScalarElem::zero() - self
    }
}

impl<'a, 'b> Mul<&'a ScalarElem> for &'b ScalarElem {
    type Output = ScalarElem;

    /// Multiply scalars.
    fn mul(self, other: &ScalarElem) -> ScalarElem {
        let mut t: ProtBuf<i64> = ProtBuf::new_zero(103);

        for i in range(0u, 52) {
            for j in range(0u, 52) {
                t[i + j] += self[i] * other[j];
            }
        }

        let mut r = ScalarElem::new_zero();
        r.reduce_weak(t[]);
        r
    }
}

impl FromPrimitive for ScalarElem {
    #[allow(unused_variables)]
    fn from_i64(n: i64) -> Option<ScalarElem> {
        None
    }

    fn from_u64(n: u64) -> Option<ScalarElem> {
        let mut s: ProtBuf8 = ProtBuf::new_zero(BYTES_SIZE);
        common::u64to8_le(s.as_mut_slice(), &n);
        ScalarElem::unpack(&s)
    }
}

impl Default for ScalarElem {
    /// Return the scalar value 0 as default.
    fn default() -> ScalarElem {
        ScalarElem::new_zero()
    }
}

impl Rand for ScalarElem {
    /// Generate a random `ScalarElem` between `[0, L-1]`, and its value
    /// is not clamped. Be sure to use a secure PRNG when calling this
    /// method. For instance `ScalarElem::new_rand()` uses urandom.
    fn rand<R: Rng>(rng: &mut R) -> ScalarElem {
        let b: ProtBuf8 = ProtBuf::new_rand(104, rng);
        ScalarElem::unpack_from_bytes(&b).unwrap()
    }
}

impl Show for ScalarElem {
    fn fmt(&self, f: &mut Formatter) -> Result {
        self.pack().fmt(f)
    }
}

impl Eq for ScalarElem {
}

impl PartialEq for ScalarElem {
    fn eq(&self, other: &ScalarElem) -> bool {
        self.pack() == other.pack()
    }
}


#[cfg(test)]
mod tests {
    use std::num::FromPrimitive;

    use tars::{ProtBuf, ProtBuf8};

    use sc::ScalarElem;


    #[test]
    fn test_ops_52() {
        let a = ScalarElem::new_rand();

        let apa = &a + &a;
        let aaa1 = &a * &apa;
        let s1 = &aaa1 - &a;

        let aa = &a * &a;
        let aaa2 = &aa + &aa;
        let s2 = &aaa2 - &a;

        assert!((&s1 - &s1).is_zero());
        assert_eq!(s1, s2);
        assert!(s1 != aaa2);
    }

    #[test]
    fn test_ops_64() {
        let n1: ProtBuf8 = ProtBuf::new_rand_os(104);
        let a = ScalarElem::unpack_from_bytes(&n1).unwrap();

        let apa = &a + &a;
        let aaa1 = &a * &apa;
        let s1 = &aaa1 - &a;

        let aa = &a * &a;
        let aaa2 = &aa + &aa;
        let s2 = &aaa2 - &a;

        assert!((&s1 - &s1).is_zero());
        assert_eq!(s1, s2);
    }

    #[test]
    fn test_ops_104() {
        let n1: ProtBuf8 = ProtBuf::new_rand_os(104);
        let a = ScalarElem::unpack_from_bytes(&n1).unwrap();

        let apa = &a + &a;
        let aaa1 = &a * &apa;
        let s1 = &aaa1 - &a;

        let aa = &a * &a;
        let aaa2 = &aa + &aa;
        let s2 = &aaa2 - &a;

        assert!((&s1 - &s1).is_zero());
        assert_eq!(s1, s2);
    }

    #[test]
    fn test_ops_52_ref() {
        let n: [u8; 52] = [
            0xf6, 0xf0, 0x53, 0xb3, 0x79, 0x46, 0x2d, 0x51,
            0xc9, 0xea, 0xcf, 0xef, 0x0e, 0x4d, 0xaa, 0xbe,
            0x17, 0xee, 0xfd, 0xf7, 0x46, 0x98, 0x1f, 0xde,
            0xbf, 0xf2, 0xe2, 0xb7, 0xdc, 0x04, 0xf5, 0xad,
            0xa5, 0x09, 0x32, 0x8d, 0x4a, 0x0a, 0x5d, 0x77,
            0x19, 0xa6, 0xce, 0xc6, 0xf0, 0x49, 0xa8, 0x00,
            0xde, 0x7d, 0x31, 0x03];

        let r: [u8; 52] = [
            0x49, 0xa8, 0x2c, 0x72, 0x5a, 0xe9, 0xd8, 0x46,
            0x04, 0x21, 0x1d, 0x07, 0xa3, 0xd1, 0x80, 0xf8,
            0xf7, 0x16, 0x2f, 0xde, 0x27, 0xde, 0xfd, 0x61,
            0x56, 0x9a, 0x70, 0x4a, 0xa6, 0x72, 0xbd, 0x43,
            0xb1, 0x86, 0xda, 0x1f, 0xc0, 0xf3, 0x8f, 0x86,
            0x30, 0x1a, 0x76, 0x81, 0xcd, 0x24, 0xcf, 0x5c,
            0xde, 0x19, 0x67, 0x03];

        let a = ScalarElem::unpack(&n.as_slice()).unwrap();
        let apa = &a + &a;
        let aaa1 = &a * &apa;
        let s = &aaa1 - &a;
        assert_eq!(s.pack()[], r[]);
    }

    #[test]
    fn test_ops_64_ref() {
        let n: [u8; 64] = [
            0xf3, 0xa5, 0x35, 0x47, 0xec, 0xcf, 0xa6, 0x84,
            0x03, 0x7f, 0xaa, 0x34, 0x62, 0x7a, 0xb6, 0x2e,
            0x18, 0xa4, 0x5c, 0xdd, 0xd7, 0x54, 0x72, 0x0b,
            0x80, 0xe5, 0xcf, 0xd4, 0x5e, 0x8a, 0x3f, 0x8e,
            0x0f, 0x6f, 0xe1, 0xbe, 0x1b, 0x6c, 0xaf, 0x45,
            0x8d, 0x51, 0xcc, 0xef, 0x87, 0xa4, 0x0d, 0x2c,
            0x87, 0xb0, 0xdd, 0x07, 0x3a, 0xf7, 0xe3, 0x16,
            0x12, 0x8c, 0x3b, 0x8b, 0x86, 0x0f, 0x78, 0xbe];

        let r: [u8; 52] = [
            0x8d, 0x44, 0xdd, 0xae, 0x17, 0xd2, 0x48, 0x44,
            0x37, 0x5a, 0x1d, 0xb7, 0x7e, 0xde, 0x28, 0xde,
            0xc6, 0x3d, 0xa6, 0xc8, 0x87, 0x9b, 0x0b, 0xf0,
            0x46, 0xba, 0xb3, 0xf8, 0x55, 0x76, 0xe5, 0xe7,
            0x2f, 0x61, 0x40, 0xb2, 0xda, 0x99, 0xf7, 0x12,
            0x9e, 0x28, 0x2f, 0xce, 0x0e, 0x34, 0xf9, 0xb2,
            0x91, 0xb3, 0x31, 0x06];

        let a = ScalarElem::unpack_from_bytes(&n.as_slice()).unwrap();
        let apa = &a + &a;
        let aaa1 = &a * &apa;
        let s = &aaa1 - &a;
        assert_eq!(s.pack()[], r[]);
    }

    #[test]
    fn test_ops_104_ref() {
        let n: [u8; 104] = [
            0x14, 0x48, 0x03, 0x95, 0x83, 0x87, 0x9a, 0x7d,
            0xb6, 0x36, 0x02, 0x97, 0xa0, 0x2c, 0x25, 0x2d,
            0xf1, 0xa1, 0xa0, 0x45, 0xa7, 0x9a, 0xef, 0x04,
            0xa9, 0x14, 0xf4, 0xb1, 0xfd, 0x24, 0x4c, 0x85,
            0x94, 0x4a, 0xd5, 0x02, 0xf8, 0x07, 0x94, 0xaf,
            0xba, 0xb9, 0x83, 0x38, 0xae, 0x59, 0xa6, 0xe3,
            0x22, 0xfa, 0xd6, 0x64, 0x8f, 0xa1, 0x92, 0x36,
            0x96, 0x29, 0xe2, 0x4e, 0x80, 0x62, 0x61, 0xda,
            0xed, 0xb2, 0x04, 0x53, 0x33, 0xca, 0xf1, 0x8f,
            0x11, 0x33, 0xed, 0x22, 0x75, 0x6a, 0x55, 0x4c,
            0x34, 0xce, 0x65, 0x94, 0xbb, 0x38, 0xe4, 0x62,
            0xe3, 0x55, 0xbb, 0x82, 0x53, 0x78, 0x87, 0x32,
            0x79, 0xbe, 0x9b, 0x23, 0x61, 0xf3, 0xf6, 0x19];

        let r: [u8; 52] = [
            0x1c, 0x2c, 0x61, 0xb6, 0xc8, 0xda, 0x85, 0x77,
            0x2b, 0x70, 0x2a, 0x54, 0xb0, 0x83, 0x49, 0xfc,
            0xc1, 0x33, 0x91, 0x37, 0x63, 0x90, 0x00, 0x13,
            0x4b, 0xde, 0x0b, 0xd2, 0x06, 0x07, 0xac, 0x54,
            0x1e, 0x3f, 0x75, 0x9f, 0x82, 0x07, 0x74, 0xd4,
            0xf5, 0x8e, 0xd8, 0xc7, 0x66, 0xcc, 0x3c, 0x23,
            0xde, 0x63, 0x9d, 0x01];

        let a = ScalarElem::unpack_from_bytes(&n.as_slice()).unwrap();
        let apa = &a + &a;
        let aaa1 = &a * &apa;
        let s = &aaa1 - &a;
        assert_eq!(s.pack()[], r[]);
    }

    #[test]
    fn test_modl_64_ref() {
        let n: [u8; 64] = [
            0xf3, 0xa5, 0x35, 0x47, 0xec, 0xcf, 0xa6, 0x84,
            0x03, 0x7f, 0xaa, 0x34, 0x62, 0x7a, 0xb6, 0x2e,
            0x18, 0xa4, 0x5c, 0xdd, 0xd7, 0x54, 0x72, 0x0b,
            0x80, 0xe5, 0xcf, 0xd4, 0x5e, 0x8a, 0x3f, 0x8e,
            0x0f, 0x6f, 0xe1, 0xbe, 0x1b, 0x6c, 0xaf, 0x45,
            0x8d, 0x51, 0xcc, 0xef, 0x87, 0xa4, 0x0d, 0x2c,
            0x87, 0xb0, 0xdd, 0x07, 0x3a, 0xf7, 0xe3, 0x16,
            0x12, 0x8c, 0x3b, 0x8b, 0x86, 0x0f, 0x78, 0xbe];

        let r: [u8; 52] = [
            0xb3, 0x98, 0xa5, 0xa3, 0x1e, 0x89, 0x39, 0xaf,
            0x6c, 0xfe, 0x18, 0x6e, 0x6f, 0xaf, 0xef, 0xea,
            0x7a, 0x52, 0xac, 0xc9, 0x43, 0xe3, 0x61, 0xff,
            0xc1, 0x51, 0x11, 0xfb, 0xe0, 0x09, 0xc6, 0x5a,
            0xa6, 0x99, 0x4a, 0xae, 0x6f, 0x5a, 0xb1, 0x45,
            0x8d, 0x51, 0xcc, 0xef, 0x87, 0xa4, 0x0d, 0x2c,
            0x87, 0xb0, 0xdd, 0x07];

        let s = ScalarElem::unpack_from_bytes(&n.as_slice()).unwrap();
        assert_eq!(s.pack()[], r[]);
    }

    #[test]
    fn test_modl_104_ref() {
        let n: [u8; 104] = [
            0x14, 0x48, 0x03, 0x95, 0x83, 0x87, 0x9a, 0x7d,
            0xb6, 0x36, 0x02, 0x97, 0xa0, 0x2c, 0x25, 0x2d,
            0xf1, 0xa1, 0xa0, 0x45, 0xa7, 0x9a, 0xef, 0x04,
            0xa9, 0x14, 0xf4, 0xb1, 0xfd, 0x24, 0x4c, 0x85,
            0x94, 0x4a, 0xd5, 0x02, 0xf8, 0x07, 0x94, 0xaf,
            0xba, 0xb9, 0x83, 0x38, 0xae, 0x59, 0xa6, 0xe3,
            0x22, 0xfa, 0xd6, 0x64, 0x8f, 0xa1, 0x92, 0x36,
            0x96, 0x29, 0xe2, 0x4e, 0x80, 0x62, 0x61, 0xda,
            0xed, 0xb2, 0x04, 0x53, 0x33, 0xca, 0xf1, 0x8f,
            0x11, 0x33, 0xed, 0x22, 0x75, 0x6a, 0x55, 0x4c,
            0x34, 0xce, 0x65, 0x94, 0xbb, 0x38, 0xe4, 0x62,
            0xe3, 0x55, 0xbb, 0x82, 0x53, 0x78, 0x87, 0x32,
            0x79, 0xbe, 0x9b, 0x23, 0x61, 0xf3, 0xf6, 0x19];

        let r: [u8; 52] = [
            0xe5, 0x43, 0x46, 0x3b, 0xb2, 0x52, 0x16, 0xc0,
            0x8a, 0xdb, 0x92, 0x72, 0xae, 0x59, 0xef, 0xaa,
            0x17, 0xb4, 0xa3, 0x3b, 0x8c, 0x88, 0xcc, 0xf6,
            0x39, 0x71, 0xc5, 0xe0, 0x1e, 0x0e, 0xe1, 0x6e,
            0x22, 0xe8, 0xf1, 0x9a, 0xf1, 0x4e, 0x0e, 0x00,
            0xd4, 0x42, 0x49, 0xcf, 0x33, 0x49, 0x07, 0xdf,
            0xb1, 0x3a, 0xee, 0x00];

        let s = ScalarElem::unpack_from_bytes(&n.as_slice()).unwrap();
        assert_eq!(s.pack()[], r[]);
    }

    #[test]
    fn test_from_u64() {
        let n: u64 = 72623859790382856;
        let b: [u8; 52] = [
            0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01,
            0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0];

        let s1 = ScalarElem::unpack(&b.as_slice()).unwrap();
        let s2 = FromPrimitive::from_u64(n).unwrap();
        assert_eq!(s1, s2);
    }
}
