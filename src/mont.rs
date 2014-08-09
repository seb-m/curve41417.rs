//! Montgomery-form Curve41417 representation
//!
//! Generate public and private keys in Montgomery's representation
//! and handle scalar multiplications.
use bytes::{B416, Bytes, MontPoint, Scalar};
use fe::FieldElem;
use sbuf::{Allocator, DefaultAllocator};


static BASEX: [u8, ..52] = [
    0x0e, 0x7c, 0xf0, 0xc1, 0x07, 0x1f, 0x7c, 0xf0,
    0xc1, 0x07, 0x1f, 0x7c, 0xf0, 0xc1, 0x07, 0x1f,
    0x7c, 0xf0, 0xc1, 0x07, 0x1f, 0x7c, 0xf0, 0xc1,
    0x07, 0x1f, 0x7c, 0xf0, 0xc1, 0x07, 0x1f, 0x7c,
    0xf0, 0xc1, 0x07, 0x1f, 0x7c, 0xf0, 0xc1, 0x07,
    0x1f, 0x7c, 0xf0, 0xc1, 0x07, 0x1f, 0x7c, 0xf0,
    0xc1, 0x07, 0x1f, 0x3c
];

static A24: [u8, ..52] = [
    0x54, 0x36, 0x68, 0xf2, 0x65, 0x83, 0x26, 0x5f,
    0x36, 0x68, 0xf2, 0x65, 0x83, 0x26, 0x5f, 0x36,
    0x68, 0xf2, 0x65, 0x83, 0x26, 0x5f, 0x36, 0x68,
    0xf2, 0x65, 0x83, 0x26, 0x5f, 0x36, 0x68, 0xf2,
    0x65, 0x83, 0x26, 0x5f, 0x36, 0x68, 0xf2, 0x65,
    0x83, 0x26, 0x5f, 0x36, 0x68, 0xf2, 0x65, 0x83,
    0x26, 0x5f, 0x36, 0x26
];

fn basex<A: Allocator>() -> MontPoint<A> {
    MontPoint(Bytes::from_bytes(BASEX).unwrap())
}

fn a24<A: Allocator>() -> FieldElem<A> {
    let b: B416<A> = Bytes::from_bytes(A24).unwrap();
    FieldElem::unpack(&b)
}


/// Compute scalar multiplication
///
/// Return a packed point `q` such that `q=n.p`, `n` is a scalar and `p` is
/// a point. On input, `n` is clamped by this function before performing
/// its scalar multiplication.
pub fn scalar_mult<A: Allocator = DefaultAllocator>(n: &Scalar<A>,
                                                    p: &MontPoint<A>)
                                                    -> MontPoint<A> {
    let mut z: B416<A>;
    let mut a: FieldElem<A>;
    let mut b: FieldElem<A>;
    let mut c: FieldElem<A>;
    let mut d: FieldElem<A>;
    let mut e: FieldElem<A>;
    let mut f: FieldElem<A>;
    let mut pe: FieldElem<A>;
    let mut r: u8;

    // Unpack p, top 2 bits are discarded in FieldElem::unpack().
    pe = FieldElem::unpack(p.get_ref());
    a = FieldElem::new();
    b = pe.clone();
    c = FieldElem::new();
    d = FieldElem::new();

    z = n.get_ref().clone();
    z.clamp_41417();

    a[0] = 1;
    d[0] = 1;

    for i in range(0u, 414).rev() {
        r = (z[i >> 3] >> (i & 7)) & 1;
        a.cswap(r as i64, &mut b);
        c.cswap(r as i64, &mut d);
        e = a + c;
        a = a - c;
        c = b + d;
        b = b - d;
        d = e.square();
        f = a.square();
        a = c * a;
        c = b * e;
        e = a + c;
        a = a - c;
        b = a.square();
        c = d - f;
        a = c * a24();
        a = a + d;
        c = c * a;
        a = d * f;
        d = b * pe;
        b = e.square();
        a.cswap(r as i64, &mut b);
        c.cswap(r as i64, &mut d);
    }

    c = c.inv();
    a = a * c;
    MontPoint(a.pack())
}

/// Compute scalar multiplication with base point
///
/// Return a packed point `q` such that `q=n.BP`. Where `BP` is the base
/// point and `n` a scalar value.
pub fn scalar_mult_base<A: Allocator = DefaultAllocator>(n: &Scalar<A>)
                                                         -> MontPoint<A> {
    scalar_mult(n, &basex())
}

/// Generate a new key pair
///
/// A new key pair `(pk, sk)` is generated. `sk` is a secret key randomly
/// generated and used as scalar value to compute the public key `pk`
/// where `pk=sk.BP` with `BP` as base point. `sk` is clamped (see
/// `B416::clamp_41417()`). The scalar value is returned wrapped in
/// `Scalar` and the public key is wrapped in `MontPoint`.
pub fn keypair<A: Allocator = DefaultAllocator>() -> (MontPoint<A>, Scalar<A>) {
    let mut sk: B416<A> = Bytes::new_rand();
    sk.clamp_41417();
    let sk_val: Scalar<A> = Scalar(sk);
    let pk_val: MontPoint<A> = scalar_mult_base(&sk_val);
    (pk_val, sk_val)
}


#[cfg(test)]
mod tests {
    use test::Bencher;

    use bytes::{B416, Bytes, Scalar};
    use mont;
    use sbuf::DefaultAllocator;


    #[test]
    fn test_dh_rand() {
        let (pk1, sk1) = mont::keypair::<DefaultAllocator>();
        let (pk2, sk2) = mont::keypair::<DefaultAllocator>();

        let ssk1w = mont::scalar_mult(&sk1, &pk2);
        let ssk2w = mont::scalar_mult(&sk2, &pk1);

        assert!(ssk1w == ssk2w);
        assert!(ssk1w.unwrap() == ssk2w.unwrap());
    }

    #[test]
    fn test_dh_ref() {
        let n: [u8, ..52] = [
            0x75, 0x47, 0x77, 0x21, 0xf3, 0xa2, 0x5f, 0x89,
            0x4b, 0x1d, 0x96, 0x01, 0xf5, 0xcb, 0x7b, 0x16,
            0xc9, 0x91, 0x95, 0x33, 0xc6, 0x2f, 0x54, 0x9a,
            0x4a, 0x8c, 0x4c, 0x1b, 0xd3, 0xef, 0xd3, 0x2d,
            0x59, 0x54, 0xcc, 0x76, 0xa2, 0x4f, 0x01, 0x87,
            0x41, 0x3e, 0x97, 0x41, 0x8d, 0x5b, 0x15, 0xf2,
            0x71, 0x4b, 0x71, 0x97];
        let r: [u8, ..52] = [
            0xce, 0x75, 0x76, 0x43, 0x9e, 0x55, 0x05, 0x27,
            0x69, 0x92, 0xc0, 0x47, 0x4f, 0x30, 0x57, 0x52,
            0x36, 0x1a, 0xd8, 0x75, 0x20, 0xb2, 0x20, 0xb9,
            0x56, 0xb6, 0xa1, 0x04, 0xe7, 0x1f, 0xaa, 0x23,
            0xc1, 0x8c, 0xc1, 0x40, 0x00, 0x18, 0x6f, 0xdd,
            0x79, 0x26, 0x67, 0x18, 0xa9, 0x07, 0x11, 0x21,
            0x84, 0xb8, 0xd7, 0x1c];

        let scn: B416<DefaultAllocator> = Bytes::from_bytes(n).unwrap();
        let scr: B416<DefaultAllocator> = Bytes::from_bytes(r).unwrap();

        let scrr = mont::scalar_mult_base(&Scalar(scn)).unwrap();
        assert!(scr == scrr);
    }

    #[bench]
    fn bench_scalar_mult_base(b: &mut Bencher) {
        let n: Scalar<DefaultAllocator> = Scalar(Bytes::new_rand());
        b.iter(|| {
            mont::scalar_mult_base(&n);
        })
    }

    #[bench]
    fn bench_scalar_mult(b: &mut Bencher) {
        let (pk, _) = mont::keypair::<DefaultAllocator>();
        let n: Scalar<DefaultAllocator> = Scalar(Bytes::new_rand());
        b.iter(|| {
            mont::scalar_mult(&n, &pk);
        })
    }
}
