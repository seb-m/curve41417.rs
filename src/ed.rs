//! Edwards-form Curve41417 representation
use serialize::hex::ToHex;
use std::default::Default;
use std::fmt::{Show, Formatter, Result};

use bytes::{B416, Bytes, EdPoint, MontPoint, Scalar, Uniformity};
use fe::FieldElem;


static BASEX: [u8, ..52] = [
    0x95, 0xc5, 0xcb, 0xf3, 0x12, 0x38, 0xfd, 0xc4,
    0x64, 0x7c, 0x53, 0xa8, 0xfa, 0x73, 0x1a, 0x30,
    0x11, 0xa1, 0x6b, 0x6d, 0x4d, 0xab, 0xa4, 0x98,
    0x54, 0xf3, 0x7f, 0xf5, 0xc7, 0x3e, 0xc0, 0x44,
    0x9f, 0x36, 0x46, 0xcd, 0x5f, 0x6e, 0x32, 0x1c,
    0x63, 0xc0, 0x18, 0x02, 0x30, 0x43, 0x14, 0x14,
    0x05, 0x49, 0x33, 0x1a];

static BASEY: [u8, ..52] = [
    0x22, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0];

static BASEZ: [u8, ..52] = [
    0x01, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0];

static BASET: [u8, ..52] = [
    0xa7, 0x3e, 0x10, 0x61, 0x84, 0x72, 0xa1, 0x29,
    0x62, 0x85, 0x16, 0x5b, 0x4a, 0x67, 0x83, 0x63,
    0x48, 0x64, 0x4b, 0x88, 0x48, 0xc0, 0xde, 0x45,
    0x3c, 0x51, 0xfe, 0x9a, 0x8e, 0x56, 0x88, 0x21,
    0x27, 0x41, 0x53, 0x43, 0xb9, 0xa8, 0xb2, 0xbe,
    0x29, 0x8d, 0x49, 0x47, 0x60, 0xec, 0xb0, 0xaa,
    0xac, 0xb2, 0xcf, 0x3a];

static B1: [u8, ..52] = [
    0x01, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0];

static BMINUS1: [u8, ..52] = [
    0xee, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0x3f];

static EDD: [u8, ..52] = [
    0x21, 0x0e, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0];

static ELLIGATORA: [u8, ..52] = [
    0xcd, 0xf1, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0x3f];

static ELLIGATORB: [u8, ..52] = [
    0x21, 0x0e, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0];

static ELLIGATORAD: [u8, ..52] = [
    0xcf, 0xf1, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0x3f];


/// A group element i.e. a point in Edwards representation.
///
/// It handle various group elements operations such as scalar
/// multiplications, point additions, Elligator point mapping,
/// key pairs generation,...
pub struct GroupElem {
  x: FieldElem,
  y: FieldElem,
  z: FieldElem,
  t: FieldElem
}

impl GroupElem {
    /// Return a new group element with all its coordinates set to zero.
    pub fn new() -> GroupElem {
        GroupElem::zero()
    }

    /// Return a group element with all its coordinates set to zero.
    pub fn zero() -> GroupElem {
        GroupElem {
            x: FieldElem::zero(),
            y: FieldElem::zero(),
            z: FieldElem::zero(),
            t: FieldElem::zero()
        }
    }

    /// Return the neutral point.
    pub fn neutral() -> GroupElem {
         GroupElem {
            x: FieldElem::zero(),
            y: FieldElem::one(),
            z: FieldElem::one(),
            t: FieldElem::zero()
         }
    }

    /// Return the base point.
    pub fn base() -> GroupElem {
        let bx: B416 = Bytes::from_bytes(BASEX).unwrap();
        let by: B416 = Bytes::from_bytes(BASEY).unwrap();
        let bz: B416 = Bytes::from_bytes(BASEZ).unwrap();
        let bt: B416 = Bytes::from_bytes(BASET).unwrap();

        GroupElem {
            x: FieldElem::unpack(&bx),
            y: FieldElem::unpack(&by),
            z: FieldElem::unpack(&bz),
            t: FieldElem::unpack(&bt)
         }
    }

    fn b1() -> B416 {
        Bytes::from_bytes(B1).unwrap()
    }

    fn bminus1() -> B416 {
        Bytes::from_bytes(BMINUS1).unwrap()
    }

    fn edd() -> FieldElem {
        let bedd: B416 = Bytes::from_bytes(EDD).unwrap();
        FieldElem::unpack(&bedd)
    }

    fn elligatora() -> FieldElem {
        let bea: B416 = Bytes::from_bytes(ELLIGATORA).unwrap();
        FieldElem::unpack(&bea)
    }

    fn elligatorb() -> FieldElem {
        let beb: B416 = Bytes::from_bytes(ELLIGATORB).unwrap();
        FieldElem::unpack(&beb)
    }

    fn elligatorad() -> FieldElem {
        let bead: B416 = Bytes::from_bytes(ELLIGATORAD).unwrap();
        FieldElem::unpack(&bead)
    }

    // Propagate changes made in x and y to z and t.
    fn propagate_from_xy(&mut self) {
        self.z = FieldElem::one();
        self.t = self.x * self.y;
    }

    /// Unpack a Curve41417 point in Edwards representation from its
    /// `bytes` representation. `bytes` must hold a packed point wrapped
    /// in `EdPoint`, usually a previous result obtained from `pack()`.
    pub fn unpack(bytes: &EdPoint) -> Option<GroupElem> {
        let b = bytes.get_ref();
        let mut r = GroupElem::new();

        // Unpack y, top 2 bits are discarded in FieldElem::unpack().
        r.y = FieldElem::unpack(b);

        // x = +/- (u/v)^((P+1)/4) = uv(uv^3)^((P-3)/4)
        // with u = 1-y^2, v = 1-dy^2
        let mut num = r.y.square();
        let mut den = num * GroupElem::edd();
        num = FieldElem::one() - num;
        den = FieldElem::one() - den;

        let mut t = den.square();
        t = t * den;
        t = num * t;
        t = t.pow4125();
        t = t * num;
        r.x = t * den;

        // Check valid sqrt
        let mut chk = r.x.square();
        chk = chk * den;
        let success = chk == num;

        // Choose between x and -x
        let mut nrx = -r.x;
        let parity = r.x.parity_bit();
        r.x.cswap(((*b.get(51) >> 7) ^ parity) as i64, &mut nrx);
        r.propagate_from_xy();

        match success {
            true => Some(r),
            false => None
        }
    }

    /// Pack a group elem's coordinate `y` along with a sign bit taken from
    /// its `x` coordinate. This packed point may be unpacked with
    /// `unpack()`.
    pub fn pack(&self) -> EdPoint {
        // Pack y
        let zi = self.z.inv();
        let tx = self.x * zi;
        let ty = self.y * zi;
        let mut r = ty.pack();

        // Sign(x): same as EdDSA25519
        *r.get_mut(51) = *r.get(51) ^ (tx.parity_bit() << 7);
        EdPoint(r)
    }

    fn cleanup(&mut self) {
        // Nothing to do.
    }

    fn cswap(&mut self, cond: i64, other: &mut GroupElem) {
        self.x.cswap(cond, &mut other.x);
        self.y.cswap(cond, &mut other.y);
        self.z.cswap(cond, &mut other.z);
        self.t.cswap(cond, &mut other.t);
    }

    /// Return point `q` such that `q=n.self` where `n` is the scalar value
    /// applied to the point `self`. Note that the value of `n` is not
    /// clamped by this method before the scalar multiplication is
    /// accomplished.
    ///
    /// This method deliberately takes as input parameter a `B416` scalar
    /// instead of a `ScalarElem` for the reason that in some cases we don't
    /// want the bits of the scalar to be modified before the scalar
    /// multiplication. Whereas a `ScalarElem` may automatically be reduced
    /// `mod L` before any scalar multiplication takes place.
    pub fn scalar_mult(&self, n: &Scalar) -> GroupElem {
        let mut p = self.clone();
        let mut q = GroupElem::neutral();

        for i in range(0u, 415).rev() {
            let c = ((*n.get(i / 8) >> (i & 7)) & 1) as i64;
            q.cswap(c, &mut p);
            p = p + q;
            q = q + q;
            q.cswap(c, &mut p);
        }
        q
    }

    /// Return point `q` such that `q=8.self` where `8` is curve's cofactor
    /// applied to this point's instance.
    pub fn scalar_mult_cofactor(&self) -> GroupElem {
        let mut q = *self + *self;
        q = q + q;
        q = q + q;
        q
    }

    /// Return point `q` such that `q=n.BP` where `n` is a scalar value applied
    /// to the base point `BP`. Note that `n` is not clamped by this method
    /// before the multiplication. Calling this method is equivalent to calling
    /// `GroupElem::base().scalar_mult(&n)`.
    pub fn scalar_mult_base(n: &Scalar) -> GroupElem {
        GroupElem::base().scalar_mult(n)
    }

    /// Return point `q` such that `q=n1.p1+n2.p2` where `n1` and `n2` are
    /// scalar values and `p1` and `p2` are group elements. Note that the
    /// values of `n1` and `n2` are not clamped by this method before their
    /// multiplications.
    pub fn double_scalar_mult(n1: &Scalar, p1: &GroupElem,
                              n2: &Scalar, p2: &GroupElem) -> GroupElem {
        p1.scalar_mult(n1) + p2.scalar_mult(n2)
    }

    /// Generate keypair `(pk, sk)` such that `pk=sk.BP` with secret scalar
    /// `sk` appropriately clamped and `pk` the resulting public key.
    pub fn keypair() -> (GroupElem, Scalar) {
        let mut sk: B416 = Bytes::new_rand();
        sk.clamp_41417();
        let sk_val = Scalar(sk);
        let pk = GroupElem::scalar_mult_base(&sk_val);
        (pk, sk_val)
    }

    /// Convert this point's coordinates to Montgomery's x-coordinate.
    /// This result may be used as input point in `curve41417::mont` scalar
    /// multiplications.
    pub fn to_mont(&self) -> MontPoint {
        let zi = self.z.inv();
        let ty = self.y * zi;
        let mut num = FieldElem::one() + ty;
        let mut den = FieldElem::one() - ty;
        den = den.inv();
        num = num * den;
        MontPoint(num.pack())
    }

    // FIXME: would there be a risk of lack of uniformity of the distribution
    // mod L if the input string r was a 52 bytes random string? At least as
    // specified in ed25519-20110926.pdf a 64 bytes input should provide
    // enough uniformity.
    fn elligator_map(n: &FieldElem) -> Option<GroupElem> {
        let mut p = GroupElem::new();

        // The input n is not defined for {-1, 1}
        let r = n.pack();
        let success: bool = (r != GroupElem::b1()) &
            (r != GroupElem::bminus1());

        // Use elligator type 2 as recommanded in:
        // https://www.mail-archive.com/curves@moderncrypto.org/msg00043.html
        // See elligator-20130828.pdf (section 5.2)
        let mut t1 = n.clone();
        t1 = t1.square();
        let mut v = FieldElem::one() - t1;
        v = v.inv();
        v = GroupElem::elligatora() * v;
        v = -v;  // v

        t1 = v.square();
        let mut e = t1 * v;
        let mut t2 = GroupElem::elligatora() * t1;
        e = e + t2;
        t1 = GroupElem::elligatorb() * v;
        e = e + t1;
        e = e.pow4139();  // e

        let is_e_minus_one: i64 = (1 - e.parity_bit()) as i64;
        let mut x = v.clone();
        t1 = -v;
        x.cswap(is_e_minus_one, &mut t1);
        t1 = FieldElem::zero();
        t2 = GroupElem::elligatora();
        t1.cswap(is_e_minus_one, &mut t2);
        x = x - t1;  // x

        let mut y2 = GroupElem::elligatorb() * x;
        let x2 = x.square();  // x2
        let mut y = GroupElem::elligatora() * x2;
        y = y + y2;
        y2 = x2 * x;
        y2 = y + y2;
        y = y2.pow4124();  // y2
        t1 = -y;
        y.cswap(1 - is_e_minus_one, &mut t1);  // y

        // Convert to Edwards coordinates: see 20080620-rennes.pdf (slide 24)
        t1 = GroupElem::elligatorb() - x2;
        t1 = t1.inv();
        t1 = y * t1;
        p.x = t1.muli(2);

        t1 = GroupElem::elligatorad() * x2;
        t2 = y2 + t1;
        t2 = t2.inv();
        t1 = y2 - t1;
        p.y = t1 * t2;

        p.propagate_from_xy();

        match success {
            true => Some(p),
            false => None
        }
    }

    /// Map a byte-string to a curve point. Return a valid group element
    /// if `n` produces to a well-defined point.
    pub fn elligator_map_from_bytes<T: Bytes + Uniformity>(n: &T)
                                                           -> Option<GroupElem> {
        GroupElem::elligator_map(&FieldElem::reduce_weak_from_bytes(n))
    }
}

impl Add<GroupElem, GroupElem> for GroupElem {
    /// Add points.
    fn add(&self, other: &GroupElem) -> GroupElem {
        // 2008/522.pdf section 3.1 (a=1)
        let a = self.x * other.x;
        let b = self.y * other.y;
        let mut c = self.t * other.t;
        c = c * GroupElem::edd();
        let d = self.z * other.z;
        let mut e = self.x + self.y;
        let mut f = other.x + other.y;
        e = e * f;
        e = e - a;
        e = e - b;
        f = d - c;
        let g = d + c;
        let h = b - a;
        GroupElem {
            x: e * f,
            y: g * h,
            z: f * g,
            t: e * h
        }
    }
}

impl Neg<GroupElem> for GroupElem {
    /// Negate point.
    fn neg(&self) -> GroupElem {
        let mut r = self.clone();
        r.x = -r.x;
        r.t = r.x * r.y;
        r
    }
}

impl Mul<Scalar, GroupElem> for GroupElem {
    /// Multiply point `self` with scalar value `other`. Note that
    /// currently it is not possible to symmetrically overload the `*`
    /// operator of a scalar value to support `scalar * point` when
    /// `point` is a `GroupElem`.
    fn mul(&self, other: &Scalar) -> GroupElem {
        self.scalar_mult(other)
    }
}

impl Drop for GroupElem {
    /// Before being released point's coordinates are zeroed-out.
    fn drop(&mut self) {
        self.cleanup();
    }
}

impl Clone for GroupElem {
    fn clone(&self) -> GroupElem {
        GroupElem {
            x: self.x.clone(),
            y: self.y.clone(),
            z: self.z.clone(),
            t: self.t.clone()
        }
    }
}

impl Default for GroupElem {
    /// By default return the neutral point.
    fn default() -> GroupElem {
        GroupElem::neutral()
    }
}

impl Show for GroupElem {
    /// Format as hex-string.
    fn fmt(&self, f: &mut Formatter) -> Result {
        self.pack().fmt(f)
    }
}

impl ToHex for GroupElem {
    fn to_hex(&self) -> String {
        self.pack().to_hex()
    }
}

impl PartialEq for GroupElem {
    /// Constant-time points equality comparison.
    fn eq(&self, other: &GroupElem) -> bool {
        self.pack().unwrap() == other.pack().unwrap()
    }
}

impl Eq for GroupElem {
}


#[cfg(test)]
mod tests {
    extern crate test;
    use self::test::Bencher;

    use bytes::{B416, B512, B832, Bytes, Scalar};
    use ed;
    use mont;


    #[test]
    fn test_dh_rand() {
        let (pk1, sk1) = ed::GroupElem::keypair();
        let (pk2, sk2) = ed::GroupElem::keypair();

        let ssk1 = pk2 * sk1;
        let ssk2 = pk1 * sk2;

        assert!(ssk1 == ssk2);
    }

    #[test]
    fn test_ops() {
        let mut b = ed::GroupElem::base();
        for _ in range(0, 10) {
            b = b + ed::GroupElem::base();
        }

        let nb = -ed::GroupElem::base();
        for _ in range(0, 10) {
            b = b + nb;
        }

        assert!(ed::GroupElem::base() == b);
    }

    #[test]
    fn test_scalar_cofactor() {
        let n: B416 = Bytes::new_rand();
        let mut cofactor: B416 = Bytes::new_zero();
        cofactor.as_mut_bytes()[0] = 0x8;

        let bp = ed::GroupElem::base();
        let q = bp * Scalar(n);
        let r = q.scalar_mult_cofactor();

        let mut s = q.clone();
        for _ in range(0, 7) {
            s = s + q;
        }
        assert!(s == r);

        s = q * Scalar(cofactor);
        assert!(s == r);
    }

    #[test]
    fn test_pack() {
        let bp = ed::GroupElem::base();
        let n = Scalar(Bytes::new_rand());

        let q = bp * n;
        let qs = q.pack();

        let zi = q.z.inv();
        let tx = q.x * zi;
        let ty = q.y * zi;
        let xs = tx.pack();
        let ys = ty.pack();

        let uq = ed::GroupElem::unpack(&qs).unwrap();

        let uys = uq.y.pack();
        assert!(ys == uys);

        let uxs = uq.x.pack();
        assert!(xs == uxs);
    }

    #[test]
    fn test_ed_to_mont() {
        let bp = ed::GroupElem::base();
        let n = Scalar(Bytes::new_rand());

        let m1 = mont::scalar_mult_base(&n);

        let mut nn = n.get_ref().clone();
        nn.clamp_41417();
        let e = bp * Scalar(nn);
        let m2 = e.to_mont();

        assert!(m1 == m2);
        assert!(m1.unwrap() == m2.unwrap());
    }

    #[test]
    fn test_elligator_map_ref() {
        let n1: [u8, ..64] = [
            0x40, 0xc9, 0x00, 0x57, 0xf5, 0xe2, 0xa2, 0x93,
            0x7c, 0x7e, 0x49, 0xbc, 0xce, 0xe4, 0xe5, 0x58,
            0x96, 0x6a, 0xf9, 0x77, 0x9f, 0x28, 0x83, 0x55,
            0x8f, 0x86, 0xf0, 0x60, 0x7f, 0x28, 0x50, 0x3c,
            0xe6, 0x2d, 0x6e, 0xdd, 0x60, 0xba, 0xe6, 0xc7,
            0xa8, 0x7c, 0x34, 0xfd, 0x03, 0xb3, 0xb5, 0xb6,
            0x17, 0x7c, 0x16, 0xdd, 0xaf, 0x34, 0xb3, 0x4a,
            0xbd, 0xa6, 0xbe, 0xf4, 0xeb, 0xed, 0x2f, 0x39];
        let x1: [u8, ..52] = [
            0x3a, 0x5b, 0x29, 0x58, 0xe5, 0x14, 0x00, 0x87,
            0x47, 0x53, 0x9b, 0x86, 0x03, 0x36, 0x77, 0xa7,
            0x51, 0xc1, 0x0d, 0x14, 0x0b, 0xe2, 0x03, 0x8e,
            0xc6, 0x1c, 0x8e, 0x62, 0x12, 0x86, 0xe9, 0xb0,
            0xfb, 0xd3, 0x97, 0xf8, 0x3f, 0x97, 0x6e, 0x56,
            0x74, 0x65, 0x5d, 0x3f, 0xe9, 0x0b, 0xe4, 0x1e,
            0xe1, 0x92, 0x86, 0x04];
        let y1: [u8, ..52] = [
            0x58, 0xb6, 0xd9, 0x2b, 0x03, 0x12, 0x5d, 0xea,
            0xa0, 0x51, 0x86, 0xef, 0x6e, 0xbd, 0x00, 0x26,
            0x9d, 0x1b, 0x79, 0xb4, 0x36, 0xd1, 0xd5, 0xa3,
            0xff, 0x9c, 0x02, 0xb3, 0xb2, 0xe2, 0xe0, 0xbe,
            0xfc, 0x55, 0x3e, 0x36, 0x30, 0xc6, 0xa9, 0x06,
            0x1a, 0x81, 0xad, 0xbc, 0x26, 0xad, 0x35, 0xeb,
            0x98, 0xc7, 0x7a, 0x35];

        let n2: [u8, ..104] = [
            0x74, 0x44, 0xd0, 0x4d, 0xba, 0xe0, 0xd1, 0x85,
            0x4d, 0x45, 0x8b, 0xdd, 0x38, 0x11, 0xa4, 0x03,
            0xfd, 0xc3, 0x7b, 0x16, 0x5c, 0x8f, 0x41, 0x92,
            0xc9, 0xc3, 0x12, 0x7d, 0xda, 0xf9, 0xc3, 0x55,
            0x9a, 0x97, 0x09, 0xb2, 0x64, 0xe8, 0x1d, 0x51,
            0xb9, 0xa4, 0x80, 0x71, 0x3d, 0x80, 0x09, 0xc0,
            0xf0, 0x5d, 0x91, 0x96, 0x3d, 0x85, 0x4d, 0x5d,
            0x42, 0xef, 0xf7, 0xca, 0x9a, 0x95, 0xa0, 0xde,
            0xd9, 0x65, 0xe2, 0xf1, 0x65, 0x76, 0x80, 0x00,
            0xd4, 0x1c, 0xf5, 0x23, 0x2e, 0x6b, 0x36, 0xad,
            0x09, 0xdb, 0xbd, 0xe7, 0x31, 0xec, 0x81, 0xf1,
            0xd5, 0x06, 0xcf, 0x32, 0x1c, 0x19, 0xe1, 0x88,
            0x55, 0xc2, 0x5a, 0x83, 0x3e, 0xec, 0xc9, 0xbb];
        let x2: [u8, ..52] = [
            0x85, 0x95, 0x7b, 0x90, 0xb9, 0x0c, 0xfc, 0x62,
            0x3a, 0xaf, 0x8e, 0xb8, 0xa2, 0x45, 0xcd, 0xaa,
            0x49, 0x4f, 0x48, 0x9f, 0x66, 0xc1, 0x9d, 0xd9,
            0x13, 0x6e, 0xd6, 0x64, 0x36, 0x6f, 0xc2, 0x2f,
            0xaf, 0xd3, 0x20, 0x6c, 0xe3, 0x0d, 0x57, 0x8b,
            0xd1, 0xf6, 0x1f, 0x1a, 0x0c, 0x73, 0x63, 0xfe,
            0xf6, 0x57, 0x4a, 0x06];
        let y2: [u8, ..52] = [
            0x3f, 0x2b, 0x7f, 0x18, 0x70, 0xc0, 0x74, 0xb4,
            0xcc, 0xa9, 0xb0, 0x7c, 0x1e, 0x44, 0xf8, 0x44,
            0x7c, 0xde, 0xa3, 0xb7, 0x97, 0xf8, 0xee, 0xae,
            0xc7, 0xd5, 0xf0, 0x11, 0x8a, 0x82, 0x11, 0xce,
            0x75, 0x82, 0x73, 0x38, 0xaf, 0x2c, 0x13, 0x19,
            0xaf, 0xdb, 0xc3, 0x37, 0xb9, 0x9f, 0x31, 0x15,
            0xb2, 0xbb, 0x1a, 0x0f];

        let nn1: B512 = Bytes::from_bytes(n1).unwrap();
        let xx1: B416 = Bytes::from_bytes(x1).unwrap();
        let yy1: B416 = Bytes::from_bytes(y1).unwrap();

        let nn2: B832 = Bytes::from_bytes(n2).unwrap();
        let xx2: B416 = Bytes::from_bytes(x2).unwrap();
        let yy2: B416 = Bytes::from_bytes(y2).unwrap();

        let p1 = ed::GroupElem::elligator_map_from_bytes(&nn1).unwrap();
        assert!(xx1 == p1.x.pack());
        assert!(yy1 == p1.y.pack());

        let p2 = ed::GroupElem::elligator_map_from_bytes(&nn2).unwrap();
        assert!(xx2 == p2.x.pack());
        assert!(yy2 == p2.y.pack());
    }

    #[test]
    fn test_dh_ref() {
        let n: [u8, ..52] = [
            0x3c, 0xe9, 0x11, 0x83, 0x62, 0xd8, 0x44, 0x96,
            0x8a, 0x6b, 0xbf, 0x76, 0x5b, 0xd2, 0x33, 0xb0,
            0xda, 0x3b, 0x89, 0x04, 0x4b, 0xd8, 0xdb, 0xc4,
            0x95, 0xe2, 0xbc, 0x01, 0xdc, 0xaf, 0x1d, 0x9a,
            0x42, 0x06, 0xd6, 0x6f, 0x9e, 0x4c, 0xfa, 0xa2,
            0x1d, 0xad, 0x2a, 0x00, 0x17, 0x94, 0x26, 0x81,
            0xe5, 0x04, 0xb3, 0x57];
        let r: [u8, ..52] = [
            0x8b, 0x1d, 0x99, 0x9e, 0xcb, 0xa5, 0x98, 0xac,
            0xb7, 0x0d, 0xa4, 0x05, 0x99, 0x65, 0xe6, 0xd1,
            0x2c, 0x73, 0xc2, 0x78, 0xef, 0x6a, 0x58, 0xac,
            0x45, 0xcb, 0x5d, 0xe5, 0xd9, 0x7c, 0xc5, 0x43,
            0xce, 0x1d, 0x04, 0xe2, 0xfd, 0x85, 0x48, 0xe4,
            0x16, 0x49, 0xe8, 0xca, 0x32, 0x72, 0x1d, 0xba,
            0x47, 0x29, 0xa5, 0x09];

        let mut scn: B416 = Bytes::from_bytes(n).unwrap();
        let scr: B416 = Bytes::from_bytes(r).unwrap();
        let bp = ed::GroupElem::base();

        scn.clamp_41417();
        let q = bp * Scalar(scn);

        assert!(q.pack().unwrap() == scr);
    }

    #[bench]
    fn bench_scalar_mult_base(b: &mut Bencher) {
        let bp = ed::GroupElem::base();
        let n = Scalar(Bytes::new_rand());
        b.iter(|| {
            bp.scalar_mult(&n);
        })
    }

    #[bench]
    fn bench_scalar_mult(b: &mut Bencher) {
        let (pk, _) = ed::GroupElem::keypair();
        let n = Scalar(Bytes::new_rand());
        b.iter(|| {
            pk.scalar_mult(&n);
        })
    }
}
