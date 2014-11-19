//! Edwards-form Curve41417 representation
use serialize::hex::ToHex;
use std::default::Default;
use std::fmt::{Show, Formatter, Result};

use bytes::{B416, Bytes, Reducible, EdPoint, Elligator, MontPoint, Scalar};
use fe::FieldElem;
use common::sbuf::{Allocator, DefaultAllocator};


const BASEX: [u8, ..52] = [
    0x95, 0xc5, 0xcb, 0xf3, 0x12, 0x38, 0xfd, 0xc4,
    0x64, 0x7c, 0x53, 0xa8, 0xfa, 0x73, 0x1a, 0x30,
    0x11, 0xa1, 0x6b, 0x6d, 0x4d, 0xab, 0xa4, 0x98,
    0x54, 0xf3, 0x7f, 0xf5, 0xc7, 0x3e, 0xc0, 0x44,
    0x9f, 0x36, 0x46, 0xcd, 0x5f, 0x6e, 0x32, 0x1c,
    0x63, 0xc0, 0x18, 0x02, 0x30, 0x43, 0x14, 0x14,
    0x05, 0x49, 0x33, 0x1a
];

const BASEY: [u8, ..52] = [
    0x22, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0
];

const BASEZ: [u8, ..52] = [
    0x01, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0
];

const BASET: [u8, ..52] = [
    0xa7, 0x3e, 0x10, 0x61, 0x84, 0x72, 0xa1, 0x29,
    0x62, 0x85, 0x16, 0x5b, 0x4a, 0x67, 0x83, 0x63,
    0x48, 0x64, 0x4b, 0x88, 0x48, 0xc0, 0xde, 0x45,
    0x3c, 0x51, 0xfe, 0x9a, 0x8e, 0x56, 0x88, 0x21,
    0x27, 0x41, 0x53, 0x43, 0xb9, 0xa8, 0xb2, 0xbe,
    0x29, 0x8d, 0x49, 0x47, 0x60, 0xec, 0xb0, 0xaa,
    0xac, 0xb2, 0xcf, 0x3a
];

const B1: [u8, ..52] = [
    0x01, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0
];

const BMINUS1: [u8, ..52] = [
    0xee, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0x3f
];

const EDD: [u8, ..52] = [
    0x21, 0x0e, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0
];

const MONTA: [u8, ..52] = [
    0x11, 0x07, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0
];

const MONTB: [u8, ..52] = [
    0x40, 0x78, 0x0c, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0
];

const MONTB1: [u8, ..52] = [
    0x76, 0xd9, 0xa0, 0xc9, 0x97, 0x0d, 0x9a, 0x7c,
    0xd9, 0xa0, 0xc9, 0x97, 0x0d, 0x9a, 0x7c, 0xd9,
    0xa0, 0xc9, 0x97, 0x0d, 0x9a, 0x7c, 0xd9, 0xa0,
    0xc9, 0x97, 0x0d, 0x9a, 0x7c, 0xd9, 0xa0, 0xc9,
    0x97, 0x0d, 0x9a, 0x7c, 0xd9, 0xa0, 0xc9, 0x97,
    0x0d, 0x9a, 0x7c, 0xd9, 0xa0, 0xc9, 0x97, 0x0d,
    0x9a, 0x7c, 0xd9, 0x18
];


/// A group element i.e. a point in Edwards representation.
///
/// It handle various group elements operations such as scalar
/// multiplications, point additions, Elligator point mapping,
/// key pairs generation,...
pub struct GroupElem<A = DefaultAllocator> {
  x: FieldElem<A>,
  y: FieldElem<A>,
  z: FieldElem<A>,
  t: FieldElem<A>
}

impl<A: Allocator> GroupElem<A> {
    /// Return a new group element with all its coordinates set to zero.
    pub fn new() -> GroupElem<A> {
        GroupElem::zero()
    }

    /// Return a group element with all its coordinates set to zero.
    pub fn zero() -> GroupElem<A> {
        GroupElem {
            x: FieldElem::zero(),
            y: FieldElem::zero(),
            z: FieldElem::zero(),
            t: FieldElem::zero()
        }
    }

    /// Return the neutral point.
    pub fn neutral() -> GroupElem<A> {
         GroupElem {
            x: FieldElem::zero(),
            y: FieldElem::one(),
            z: FieldElem::one(),
            t: FieldElem::zero()
         }
    }

    /// Return the base point `(x, 34)` of prime order `L`.
    pub fn base() -> GroupElem<A> {
        let bx: B416<A> = Bytes::from_bytes(&BASEX).unwrap();
        let by: B416<A> = Bytes::from_bytes(&BASEY).unwrap();
        let bz: B416<A> = Bytes::from_bytes(&BASEZ).unwrap();
        let bt: B416<A> = Bytes::from_bytes(&BASET).unwrap();

        GroupElem {
            x: FieldElem::unpack(&bx),
            y: FieldElem::unpack(&by),
            z: FieldElem::unpack(&bz),
            t: FieldElem::unpack(&bt)
         }
    }

    fn b1() -> B416<A> {
        Bytes::from_bytes(&B1).unwrap()
    }

    fn bminus1() -> B416<A> {
        Bytes::from_bytes(&BMINUS1).unwrap()
    }

    fn edd() -> FieldElem<A> {
        let bedd: B416<A> = Bytes::from_bytes(&EDD).unwrap();
        FieldElem::unpack(&bedd)
    }

    fn monta() -> FieldElem<A> {
        let a: B416<A> = Bytes::from_bytes(&MONTA).unwrap();
        FieldElem::unpack(&a)
    }

    fn montb() -> FieldElem<A> {
        let b: B416<A> = Bytes::from_bytes(&MONTB).unwrap();
        FieldElem::unpack(&b)
    }

    fn montb1() -> FieldElem<A> {
        let b1: B416<A> = Bytes::from_bytes(&MONTB1).unwrap();
        FieldElem::unpack(&b1)
    }

    // Propagate changes made in x and y to z and t.
    fn propagate_from_xy(&mut self) {
        self.z = FieldElem::one();
        self.t = self.x * self.y;
    }

    /// Unpack a Curve41417 point in Edwards representation from its
    /// `bytes` representation. `bytes` must hold a packed point wrapped
    /// in `EdPoint`, usually a previous result obtained from `pack()`.
    pub fn unpack(bytes: &EdPoint<A>) -> Option<GroupElem<A>> {
        let b = bytes.get();
        let mut r: GroupElem<A> = GroupElem::new();

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
        r.x.cswap(((b[51] >> 7) ^ parity) as i64, &mut nrx);
        r.propagate_from_xy();

        match success {
            true => Some(r),
            false => None
        }
    }

    /// Pack a group elem's coordinate `y` along with a sign bit taken from
    /// its `x` coordinate. This packed point may later be unpacked with
    /// `unpack()`.
    pub fn pack(&self) -> EdPoint<A> {
        // Pack y
        let zi = self.z.inv();
        let tx = self.x * zi;
        let ty = self.y * zi;
        let mut r = ty.pack();

        // Sign(x): same as EdDSA25519
        r[51] = r[51] ^ (tx.parity_bit() << 7);
        EdPoint(r)
    }

    fn cleanup(&mut self) {
        // Nothing to do.
    }

    fn cswap(&mut self, cond: i64, other: &mut GroupElem<A>) {
        self.x.cswap(cond, &mut other.x);
        self.y.cswap(cond, &mut other.y);
        self.z.cswap(cond, &mut other.z);
        self.t.cswap(cond, &mut other.t);
    }

    /// Return a point `q` such that `q=n.self` where `n` is the scalar
    /// value applied to the point `self`. Note that the value of `n` is
    /// not clamped by this method before the scalar multiplication is
    /// accomplished. Especially no cofactor multiplication is implicitly
    /// applied. Use `scalar_mult_cofactor()` prior to calling this method
    /// to explictly pre-cofactor this point.
    ///
    /// This method deliberately takes as input parameter a `B416` scalar
    /// instead of a `ScalarElem` for the reason that in some cases we don't
    /// want the bits of the scalar to be modified before any scalar
    /// multiplication. Whereas a `ScalarElem` would automatically be reduced
    /// `mod L` (see `base()`) before any scalar multiplication takes place.
    pub fn scalar_mult(&self, n: &Scalar<A>) -> GroupElem<A> {
        let mut p = self.clone();
        let mut q: GroupElem<A> = GroupElem::neutral();

        for i in range(0u, 415).rev() {
            let c = ((n[i / 8] >> (i & 7)) & 1) as i64;
            q.cswap(c, &mut p);
            p = p + q;
            q = q + q;
            q.cswap(c, &mut p);
        }
        q
    }

    /// Return a point `q` such that `q=8.self` where `8` is curve's cofactor
    /// applied to this point's instance.
    pub fn scalar_mult_cofactor(&self) -> GroupElem<A> {
        let mut q = *self + *self;
        q = q + q;
        q = q + q;
        q
    }

    /// Return point `q` such that `q=n.BP` where `n` is a scalar value applied
    /// to the base point `BP`. Note that `n` is not clamped by this method
    /// before the multiplication. Calling this method is equivalent to calling
    /// `GroupElem::base().scalar_mult(&n)`.
    pub fn scalar_mult_base(n: &Scalar<A>) -> GroupElem<A> {
        GroupElem::base().scalar_mult(n)
    }

    /// Return point `q` such that `q=n1.p1+n2.p2` where `n1` and `n2` are
    /// scalar values and `p1` and `p2` are group elements. Note that the
    /// values of `n1` and `n2` are not clamped by this method before their
    /// multiplications.
    pub fn double_scalar_mult(n1: &Scalar<A>, p1: &GroupElem<A>,
                              n2: &Scalar<A>, p2: &GroupElem<A>)
                              -> GroupElem<A> {
        p1.scalar_mult(n1) + p2.scalar_mult(n2)
    }

    /// Generate keypair `(pk, sk)` such that `pk=sk.BP` with secret scalar
    /// `sk` appropriately clamped and `pk` is the resulting public key.
    pub fn keypair() -> (GroupElem<A>, Scalar<A>) {
        let mut sk: B416<A> = Bytes::new_rand();
        sk.clamp_41417();
        let sk_val: Scalar<A> = Scalar(sk);
        let pk = GroupElem::scalar_mult_base(&sk_val);
        (pk, sk_val)
    }

    /// Convert this point Edwards coordinates to Montgomery's
    /// x-coordinate. This result may be used as input point in
    /// `curve41417::mont` scalar multiplications.
    pub fn to_mont(&self) -> MontPoint<A> {
        let zi = self.z.inv();
        let ty = self.y * zi;

        // u = (1 + y) / (1 - y)
        let mut num = FieldElem::one() + ty;
        let mut den = FieldElem::one() - ty;
        den = den.inv();
        num = num * den;
        MontPoint(num.pack())
    }

    /// Use [Elligator](http://elligator.cr.yp.to/) to encode a curve
    /// point to a byte-string representation.
    pub fn elligator_to_representation(&self) -> Option<Elligator<A>> {
        // Use the following isomorphism:
        //  Eed: x^2 + y^2 = 1 + 3617 x^2 * y^2
        //  Ew:  v^2 = u^3 + A*u^2 + B*u
        //
        // With:
        //  d=3617
        //  A1=2*(1+d)/(1-d)
        //  B1=4/(1-d)
        //  A=A1/B1
        //  B=1/B1^2
        //
        // Points conversions:
        //  u=(1+y)/B1*(1-y)
        //  v=u/x=(1+y)/(B*x*(1-y))
        //  x=u/v
        //  y=(B1*u-1)/(B1*u+1)

        // Convert coordinates.
        let mut t0 = self.z - self.y;
        t0 = GroupElem::montb1() * t0;
        let mut t1 = self.z + self.y;

        let mut u = t0.inv();
        u = t1 * u;  // u

        t0 = self.x * t0;
        let mut v = t0.inv();
        v = t1 * v;
        v = self.z * v;  // v

        // Few remarks:
        //
        // - Use elligator type 2 as recommanded in:
        //   https://www.mail-archive.com/curves@moderncrypto.org/msg00043.html
        //
        // - Employ the same terminology used in elligator-20130828.pdf
        //   section 5.2 with u=-1.
        //
        // - See https://www.imperialviolet.org/2013/12/25/elligator.html
        //   for more details on c.
        //
        //   c=(u(u+A)^3)^((q-3)/4) where c, c^2 and c^3 will be used in the
        //   following computations.
        //
        // - Don't check special cases x!=0 and y=0 => x=0, there are very
        //   unlikely.
        let upa = u + GroupElem::monta();
        let mut c = upa.square();
        c = c * upa;
        c = c * u;
        let mut r2 = c.clone();
        let mut t = c.clone();
        c = c.pow4125();  // c

        // Check u(u+A) is a square i.e. (u*(u+A))^((q-1)/2)=u*(u+A)^3*c^2=1
        t1 = c.square();
        t = t1 * t;  // t
        if t.parity_bit() == 0 {
            return None;
        }

        // First square root r1=(u/(u+A))^((q+1)/4)=u*(u+A)*c
        let mut r1 = upa * u;
        r1 = r1 * c;  // r1

        // Second square root r2=((u+A)/u)^((q+1)/4)=u*(u+A)^5*c^3
        t0 = upa.square();
        r2 = r2 * t0;
        r2 = r2 * t1;
        r2 = r2 * c;  // r2

        // Choose between r1 and r2 by testing if v is itself a square.
        // Note: checking if v < (q+1)/2 would be more efficient than
        //       taking the Legendre symbol.
        let rc = v.pow4139();
        r2.cswap(rc.parity_bit() as i64, &mut r1);
        Some(Elligator(r2.pack()))
    }

    fn elligator_from_fe(n: &FieldElem<A>) -> Option<GroupElem<A>> {
        // Check n not in {-1, 1} (A^2-4B is a non-square in Fq).
        let r = n.pack();
        if r == GroupElem::b1() || r == GroupElem::bminus1() {
            return None;
        }

        // See comments in elligator_to_representation().
        let mut t1 = n.square();
        let mut v = FieldElem::one() - t1;
        v = v.inv();
        v = GroupElem::monta() * v;
        v = -v;  // v

        t1 = v.square();
        let mut e = t1 * v;
        let mut t2 = GroupElem::monta() * t1;
        e = e + t2;
        t1 = GroupElem::montb() * v;
        e = e + t1;
        e = e.pow4139();  // e

        let is_e_minus_one: i64 = (1 - e.parity_bit()) as i64;
        let mut x = v.clone();
        t1 = -v;
        x.cswap(is_e_minus_one, &mut t1);
        t1 = FieldElem::zero();
        t2 = GroupElem::monta();
        t1.cswap(is_e_minus_one, &mut t2);
        x = x - t1;  // x

        let mut y2 = GroupElem::montb() * x;
        let x2 = x.square();  // x^2
        let mut y = GroupElem::monta() * x2;
        y = y + y2;
        y2 = x2 * x;
        y2 = y + y2;  // y^2
        y = y2.pow4124();
        t1 = -y;
        y.cswap(1 - is_e_minus_one, &mut t1);  // y

        // Convert to Edwards coordinates.
        let mut p: GroupElem<A> = GroupElem::new();
        t1 = y.inv();
        p.x = x * t1;

        t1 = GroupElem::montb1() * x;
        t2 = t1 + FieldElem::one();
        t2 = t2.inv();
        t1 = t1 - FieldElem::one();
        p.y = t1 * t2;

        p.propagate_from_xy();
        Some(p)
    }

    /// Map a byte-string representation to a curve point. Return a valid
    /// group element if it produces to a well-defined point.
    ///
    /// The argument provided to this method is expected to originate from
    /// the encoded representation returned by
    /// `elligator_to_representation()`.
    pub fn elligator_from_representation(r: &Elligator<A>)
                                         -> Option<GroupElem<A>> {
        GroupElem::elligator_from_fe(&FieldElem::unpack(r.get()))
    }

    /// Map a byte-string to a curve point. Return a valid group element
    /// if `s` produces to a well-defined point. The provided input is
    /// first reduced in `Fq`. For better uniformity of the distribution
    /// in `Fq` the input must be sufficiently large.
    ///
    /// Note that since `ψ(r) = ψ(-r)` with `ψ` the mapping function and
    /// `r = s mod q`, as `r` and `-r` map to the same point, it may lead
    /// to obtain a non unique result for
    /// `elligator_to_representation(elligator_from_bytes(s))` in `{r, -r}`.
    pub fn elligator_from_bytes<T: Bytes + Reducible>(s: &T)
                                                      -> Option<GroupElem<A>> {
        GroupElem::elligator_from_fe(&FieldElem::reduce_weak_from_bytes(s))
    }
}

impl<A: Allocator> Add<GroupElem<A>, GroupElem<A>> for GroupElem<A> {
    /// Add points.
    fn add(&self, other: &GroupElem<A>) -> GroupElem<A> {
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

impl<A: Allocator> Sub<GroupElem<A>, GroupElem<A>> for GroupElem<A> {
    /// Subtract points.
    fn sub(&self, other: &GroupElem<A>) -> GroupElem<A> {
        *self + (-(*other))
    }
}

impl<A: Allocator> Neg<GroupElem<A>> for GroupElem<A> {
    /// Negate point.
    fn neg(&self) -> GroupElem<A> {
        let mut r = self.clone();
        r.x = -r.x;
        r.t = -r.t;
        r
    }
}

impl<A: Allocator> Mul<Scalar<A>, GroupElem<A>> for GroupElem<A> {
    /// Multiply point `self` with scalar value `other`. Note that
    /// currently it is not possible to symmetrically overload the `*`
    /// operator of a scalar value to support `scalar * point` when
    /// `point` is a `GroupElem`.
    fn mul(&self, other: &Scalar<A>) -> GroupElem<A> {
        self.scalar_mult(other)
    }
}

#[unsafe_destructor]
impl<A: Allocator> Drop for GroupElem<A> {
    /// Before being released point's coordinates are zeroed-out.
    fn drop(&mut self) {
        self.cleanup();
    }
}

impl<A: Allocator> Clone for GroupElem<A> {
    fn clone(&self) -> GroupElem<A> {
        GroupElem {
            x: self.x.clone(),
            y: self.y.clone(),
            z: self.z.clone(),
            t: self.t.clone()
        }
    }
}

impl<A: Allocator> Default for GroupElem<A> {
    /// By default return the neutral point.
    fn default() -> GroupElem<A> {
        GroupElem::neutral()
    }
}

impl<A: Allocator> Show for GroupElem<A> {
    /// Format as hex-string.
    fn fmt(&self, f: &mut Formatter) -> Result {
        self.pack().fmt(f)
    }
}

impl<A: Allocator> ToHex for GroupElem<A> {
    fn to_hex(&self) -> String {
        self.pack().to_hex()
    }
}

impl<A: Allocator> PartialEq for GroupElem<A> {
    /// Constant-time points equality comparison.
    fn eq(&self, other: &GroupElem<A>) -> bool {
        self.pack().unwrap() == other.pack().unwrap()
    }
}

impl<A: Allocator> Eq for GroupElem<A> {
}


#[cfg(test)]
mod tests {
    use test::Bencher;

    use common::sbuf::DefaultAllocator;

    use bytes::{B416, B512, Bytes, Scalar, Elligator};
    use ed;
    use mont;


    #[test]
    fn test_dh_rand() {
        let (pk1, sk1) = ed::GroupElem::<DefaultAllocator>::keypair();
        let (pk2, sk2) = ed::GroupElem::<DefaultAllocator>::keypair();

        let ssk1 = pk2 * sk1;
        let ssk2 = pk1 * sk2;

        assert!(ssk1 == ssk2);
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

        let mut scn: B416<DefaultAllocator> = Bytes::from_bytes(&n).unwrap();
        let scr: B416<DefaultAllocator> = Bytes::from_bytes(&r).unwrap();
        let bp = ed::GroupElem::<DefaultAllocator>::base();

        scn.clamp_41417();
        let q = bp * Scalar(scn);

        assert!(q.pack().unwrap() == scr);
    }

    #[test]
    fn test_ops() {
        let mut b = ed::GroupElem::<DefaultAllocator>::base();
        for _ in range(0u, 10) {
            b = b + ed::GroupElem::<DefaultAllocator>::base();
        }

        let nb = ed::GroupElem::<DefaultAllocator>::base();
        for _ in range(0u, 10) {
            b = b - nb;
        }

        assert!(ed::GroupElem::base() == b);
    }

    #[test]
    fn test_scalar_cofactor() {
        let n: B416<DefaultAllocator> = Bytes::new_rand();
        let mut cofactor: B416<DefaultAllocator> = Bytes::new_zero();
        cofactor[0] = 0x8;

        let bp = ed::GroupElem::<DefaultAllocator>::base();
        let q = bp * Scalar(n);
        let r = q.scalar_mult_cofactor();

        let mut s = q.clone();
        for _ in range(0u, 7) {
            s = s + q;
        }
        assert!(s == r);

        s = q * Scalar::<DefaultAllocator>(cofactor);
        assert!(s == r);
    }

    #[test]
    fn test_pack() {
        let bp = ed::GroupElem::<DefaultAllocator>::base();
        let n = Scalar::<DefaultAllocator>(Bytes::new_rand());

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
        let bp = ed::GroupElem::<DefaultAllocator>::base();
        let mut b1: B416<DefaultAllocator> = Bytes::new_rand();
        b1.clamp_41417();
        let n1 = Scalar(b1);

        let m1 = mont::scalar_mult_base(&n1);
        let e1 = bp * n1;
        let m11 = e1.to_mont();

        assert!(m1 == m11);
        assert!(m1.unwrap() == m11.unwrap());
    }

    #[test]
    fn test_elligator_ref_52() {
        let n: [u8, ..52] = [
            0x40, 0xc9, 0x00, 0x57, 0xf5, 0xe2, 0xa2, 0x93,
            0x7c, 0x7e, 0x49, 0xbc, 0xce, 0xe4, 0xe5, 0x58,
            0x96, 0x6a, 0xf9, 0x77, 0x9f, 0x28, 0x83, 0x55,
            0x8f, 0x86, 0xf0, 0x60, 0x7f, 0x28, 0x50, 0x3c,
            0xe6, 0x2d, 0x6e, 0xdd, 0x60, 0xba, 0xe6, 0xc7,
            0xa8, 0x7c, 0x34, 0xfd, 0x03, 0xb3, 0xb5, 0xb6,
            0x17, 0x7c, 0x16, 0x15];

        let x: [u8, ..52] = [
            0x20, 0xfc, 0x3e, 0x88, 0xf8, 0x54, 0x17, 0xdf,
            0xe3, 0x43, 0x89, 0x7f, 0x4b, 0xdf, 0xe5, 0xcd,
            0xd8, 0xae, 0x9c, 0x3a, 0xc9, 0x3a, 0x0d, 0xc2,
            0x80, 0xf7, 0x1e, 0x5a, 0x02, 0x75, 0x99, 0x8c,
            0x80, 0x84, 0xa4, 0x43, 0x27, 0x6a, 0x07, 0xef,
            0x6f, 0x32, 0x3e, 0x5f, 0x17, 0x30, 0xa9, 0x70,
            0xb4, 0x42, 0xcc, 0x0a];

        let y: [u8, ..52] = [
            0x81, 0x59, 0x34, 0xcd, 0xd9, 0xaf, 0x26, 0xf8,
            0xaf, 0xa6, 0xe5, 0xa4, 0xcd, 0x91, 0x58, 0x82,
            0xbf, 0x90, 0xa7, 0x7e, 0x6e, 0xc8, 0x27, 0x38,
            0x49, 0xf5, 0x8e, 0xe2, 0x97, 0x85, 0x20, 0x7b,
            0x9c, 0xf9, 0x28, 0x44, 0xf1, 0x74, 0x93, 0x7f,
            0x7e, 0xd9, 0xec, 0xbb, 0xe7, 0xff, 0x1b, 0xae,
            0xd0, 0x11, 0xd4, 0x1c];

        let n1: Elligator<DefaultAllocator> =
            Elligator(Bytes::from_bytes(&n).unwrap());
        let xx: B416<DefaultAllocator> = Bytes::from_bytes(&x).unwrap();
        let yy: B416<DefaultAllocator> = Bytes::from_bytes(&y).unwrap();

        let p = ed::GroupElem::elligator_from_representation(&n1).unwrap();
        assert!(xx == p.x.pack());
        assert!(yy == p.y.pack());

        let n2 = p.elligator_to_representation().unwrap();
        assert!(n1 == n2);
    }

    #[test]
    fn test_elligator_ref_64() {
        let n: [u8, ..64] = [
            0x40, 0xc9, 0x00, 0x57, 0xf5, 0xe2, 0xa2, 0x93,
            0x7c, 0x7e, 0x49, 0xbc, 0xce, 0xe4, 0xe5, 0x58,
            0x96, 0x6a, 0xf9, 0x77, 0x9f, 0x28, 0x83, 0x55,
            0x8f, 0x86, 0xf0, 0x60, 0x7f, 0x28, 0x50, 0x3c,
            0xe6, 0x2d, 0x6e, 0xdd, 0x60, 0xba, 0xe6, 0xc7,
            0xa8, 0x7c, 0x34, 0xfd, 0x03, 0xb3, 0xb5, 0xb6,
            0x17, 0x7c, 0x16, 0xdd, 0xaf, 0x34, 0xb3, 0x4a,
            0xbd, 0xa6, 0xbe, 0xf4, 0xeb, 0xed, 0x2f, 0x39];

        let x: [u8, ..52] = [
            0x62, 0x1e, 0xdf, 0x72, 0x6a, 0xc4, 0xc3, 0xd9,
            0x11, 0x9a, 0x53, 0xb6, 0xc0, 0x8d, 0xb1, 0x43,
            0xa3, 0x5a, 0x24, 0x6a, 0xde, 0xe8, 0x16, 0x5a,
            0xfd, 0xdb, 0x15, 0xec, 0xf7, 0xbc, 0xe7, 0x57,
            0x25, 0xcc, 0x62, 0xfc, 0x38, 0xec, 0xa7, 0xcd,
            0x33, 0x33, 0x44, 0x26, 0xd1, 0x43, 0x68, 0xb6,
            0xb8, 0xe7, 0xf2, 0x23];

        let y: [u8, ..52] = [
            0x99, 0xe7, 0xfb, 0x51, 0x6b, 0x3e, 0x55, 0x0c,
            0x2d, 0xf7, 0xa5, 0x61, 0xad, 0x8b, 0x29, 0x1d,
            0xbf, 0xd3, 0x98, 0x77, 0x90, 0x83, 0x11, 0x5f,
            0x30, 0x31, 0x29, 0xdb, 0xc2, 0x59, 0x22, 0xf9,
            0x83, 0x56, 0xcc, 0x40, 0x7b, 0x98, 0xc1, 0x98,
            0x87, 0x59, 0xfd, 0xf2, 0xd7, 0xd5, 0xac, 0xff,
            0x2f, 0xad, 0x3c, 0x3b];

        let r1: [u8, ..52] = [
            0xef, 0xc7, 0x9a, 0x2e, 0x3d, 0x2d, 0x47, 0x96,
            0x29, 0xb1, 0x04, 0xed, 0xdd, 0xe4, 0xe5, 0x58,
            0x96, 0x6a, 0xf9, 0x77, 0x9f, 0x28, 0x83, 0x55,
            0x8f, 0x86, 0xf0, 0x60, 0x7f, 0x28, 0x50, 0x3c,
            0xe6, 0x2d, 0x6e, 0xdd, 0x60, 0xba, 0xe6, 0xc7,
            0xa8, 0x7c, 0x34, 0xfd, 0x03, 0xb3, 0xb5, 0xb6,
            0x17, 0x7c, 0x16, 0x1d];

        let r2: [u8, ..52] = [
            0x00, 0x38, 0x65, 0xd1, 0xc2, 0xd2, 0xb8, 0x69,
            0xd6, 0x4e, 0xfb, 0x12, 0x22, 0x1b, 0x1a, 0xa7,
            0x69, 0x95, 0x06, 0x88, 0x60, 0xd7, 0x7c, 0xaa,
            0x70, 0x79, 0x0f, 0x9f, 0x80, 0xd7, 0xaf, 0xc3,
            0x19, 0xd2, 0x91, 0x22, 0x9f, 0x45, 0x19, 0x38,
            0x57, 0x83, 0xcb, 0x02, 0xfc, 0x4c, 0x4a, 0x49,
            0xe8, 0x83, 0xe9, 0x22];

        let n1: B512<DefaultAllocator> = Bytes::from_bytes(&n).unwrap();
        let xx: B416<DefaultAllocator> = Bytes::from_bytes(&x).unwrap();
        let yy: B416<DefaultAllocator> = Bytes::from_bytes(&y).unwrap();
        let rr1: Elligator<DefaultAllocator> =
            Elligator(Bytes::from_bytes(&r1).unwrap());
        let rr2: Elligator<DefaultAllocator> =
            Elligator(Bytes::from_bytes(&r2).unwrap());

        let p = ed::GroupElem::elligator_from_bytes(&n1).unwrap();
        assert!(xx == p.x.pack());
        assert!(yy == p.y.pack());

        let r = p.elligator_to_representation().unwrap();
        assert!(r == rr1 || r == rr2);
    }

    #[test]
    fn test_elligator_s2p() {
        let b: B512<DefaultAllocator> = Bytes::new_rand();
        let p1: ed::GroupElem<DefaultAllocator> =
            ed::GroupElem::elligator_from_bytes(&b).unwrap();
        let r = p1.elligator_to_representation().unwrap();
        let p2 = ed::GroupElem::elligator_from_representation(&r).unwrap();
        assert!(p1 == p2);
    }

    #[test]
    fn test_elligator_p2s() {
        let mut p1: ed::GroupElem<DefaultAllocator>;
        let mut e: Elligator<DefaultAllocator>;
        loop {
            let (p, _) = ed::GroupElem::<DefaultAllocator>::keypair();
            let r = p.elligator_to_representation();
            if r.is_some() {
                e = r.unwrap();
                p1 = p.clone();
                break;
            }
        }
        let p2 = ed::GroupElem::elligator_from_representation(&e).unwrap();
        assert!(p1 == p2);
    }

    #[bench]
    fn bench_scalar_mult_base(b: &mut Bencher) {
        let bp = ed::GroupElem::<DefaultAllocator>::base();
        let n = Scalar::<DefaultAllocator>(Bytes::new_rand());
        b.iter(|| {
            bp.scalar_mult(&n);
        })
    }

    #[bench]
    fn bench_scalar_mult(b: &mut Bencher) {
        let (pk, _) = ed::GroupElem::<DefaultAllocator>::keypair();
        let n = Scalar::<DefaultAllocator>(Bytes::new_rand());
        b.iter(|| {
            pk.scalar_mult(&n);
        })
    }
}
