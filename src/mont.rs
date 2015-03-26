//! Montgomery-form Curve41417 representation
//!
//! Generate public and secret keys in Montgomery's representation and
//! handle scalar multiplications.
use std::convert::AsRef;

use tars::{ProtBuf, ProtBuf8, ProtKey8};

use common::{SCALAR_SIZE, Scalar};
use fe::FieldElem;


const BASEX: [u8; 52] = [
    0x0e, 0x7c, 0xf0, 0xc1, 0x07, 0x1f, 0x7c, 0xf0,
    0xc1, 0x07, 0x1f, 0x7c, 0xf0, 0xc1, 0x07, 0x1f,
    0x7c, 0xf0, 0xc1, 0x07, 0x1f, 0x7c, 0xf0, 0xc1,
    0x07, 0x1f, 0x7c, 0xf0, 0xc1, 0x07, 0x1f, 0x7c,
    0xf0, 0xc1, 0x07, 0x1f, 0x7c, 0xf0, 0xc1, 0x07,
    0x1f, 0x7c, 0xf0, 0xc1, 0x07, 0x1f, 0x7c, 0xf0,
    0xc1, 0x07, 0x1f, 0x3c
];

const A24: [u8; 52] = [
    0x54, 0x36, 0x68, 0xf2, 0x65, 0x83, 0x26, 0x5f,
    0x36, 0x68, 0xf2, 0x65, 0x83, 0x26, 0x5f, 0x36,
    0x68, 0xf2, 0x65, 0x83, 0x26, 0x5f, 0x36, 0x68,
    0xf2, 0x65, 0x83, 0x26, 0x5f, 0x36, 0x68, 0xf2,
    0x65, 0x83, 0x26, 0x5f, 0x36, 0x68, 0xf2, 0x65,
    0x83, 0x26, 0x5f, 0x36, 0x68, 0xf2, 0x65, 0x83,
    0x26, 0x5f, 0x36, 0x26
];

fn a24() -> FieldElem {
    FieldElem::unpack(&A24).unwrap()
}


/// Compute scalar multiplication
///
/// Return a packed point `q` such that `q=n.p`, `n` is a scalar and `p` is
/// a point. On input, `n` is clamped before performing the scalar
/// multiplication.
pub fn scalar_mult<T: AsRef<[u8]>, U: AsRef<[u8]>>(n: &T, p: &U) -> ProtBuf8 {
    let mut z: ProtBuf8;
    let mut a: FieldElem;
    let mut b: FieldElem;
    let mut c: FieldElem;
    let mut d: FieldElem;
    let mut e: FieldElem;
    let mut f: FieldElem;
    let mut pe: FieldElem;
    let mut r: u8;

    // Unpack p, top 2 bits are discarded in FieldElem::unpack().
    pe = FieldElem::unpack(p.as_ref()).unwrap();
    a = FieldElem::new();
    b = pe.clone();
    c = FieldElem::new();
    d = FieldElem::new();

    z = ProtBuf::from_slice(n.as_ref());
    z.clamp_41417();

    a[0] = 1;
    d[0] = 1;

    for i in (0_usize..414).rev() {
        r = (z[i >> 3] >> (i & 7)) & 1;
        a.cswap(r as i64, &mut b);
        c.cswap(r as i64, &mut d);
        e = &a + &c;
        a = a - &c;
        c = &b + &d;
        b = b - &d;
        d = e.square();
        f = a.square();
        a = &a * &c;
        c = &b * &e;
        e = &a + &c;
        a = a - &c;
        b = a.square();
        c = &d - &f;
        a = &c * &a24();
        a = a + &d;
        c = &c * &a;
        a = &d * &f;
        d = &b * &pe;
        b = e.square();
        a.cswap(r as i64, &mut b);
        c.cswap(r as i64, &mut d);
    }

    c = c.inv();
    a = &a * &c;
    a.pack()
}

/// Compute scalar multiplication with base point
///
/// Return a packed point `q` such that `q=n.BP`. Where `BP` is the base
/// point and `n` a scalar value.
pub fn scalar_mult_base<T: AsRef<[u8]>>(n: &T) -> ProtBuf8 {
    scalar_mult(n, &BASEX.as_ref())
}

/// Generate a new secret key
///
/// A new secret key is randomly generated, clamped and returned. It can be
/// used as scalar value to compute a public key `pk` such that `pk=sk.BP`
/// with `BP` as base point by calling `scalar_mult_base()`.
pub fn gen_key() -> ProtKey8 {
    let mut sk = ProtBuf::new_rand_os(SCALAR_SIZE);
    sk.clamp_41417();
    sk.into_key()
}


#[cfg(test)]
mod tests {
    use test::Bencher;

    use tars::{ProtBuf, ProtBuf8};

    use common::SCALAR_SIZE;
    use mont;


    #[test]
    fn test_dh_rand() {
        let sk1 = mont::gen_key();
        let pk1 = mont::scalar_mult_base(&sk1.read());
        let sk2 = mont::gen_key();
        let pk2 = mont::scalar_mult_base(&sk2.read());

        let ssk1w = mont::scalar_mult(&sk1.read(), &pk2);
        let ssk2w = mont::scalar_mult(&sk2.read(), &pk1);

        assert_eq!(ssk1w, ssk2w);
        assert_eq!(ssk1w.as_ref(), ssk2w.as_ref());
    }

    #[test]
    fn test_dh_ref() {
        let n: [u8; 52] = [
            0x75, 0x47, 0x77, 0x21, 0xf3, 0xa2, 0x5f, 0x89,
            0x4b, 0x1d, 0x96, 0x01, 0xf5, 0xcb, 0x7b, 0x16,
            0xc9, 0x91, 0x95, 0x33, 0xc6, 0x2f, 0x54, 0x9a,
            0x4a, 0x8c, 0x4c, 0x1b, 0xd3, 0xef, 0xd3, 0x2d,
            0x59, 0x54, 0xcc, 0x76, 0xa2, 0x4f, 0x01, 0x87,
            0x41, 0x3e, 0x97, 0x41, 0x8d, 0x5b, 0x15, 0xf2,
            0x71, 0x4b, 0x71, 0x97];
        let r: [u8; 52] = [
            0xce, 0x75, 0x76, 0x43, 0x9e, 0x55, 0x05, 0x27,
            0x69, 0x92, 0xc0, 0x47, 0x4f, 0x30, 0x57, 0x52,
            0x36, 0x1a, 0xd8, 0x75, 0x20, 0xb2, 0x20, 0xb9,
            0x56, 0xb6, 0xa1, 0x04, 0xe7, 0x1f, 0xaa, 0x23,
            0xc1, 0x8c, 0xc1, 0x40, 0x00, 0x18, 0x6f, 0xdd,
            0x79, 0x26, 0x67, 0x18, 0xa9, 0x07, 0x11, 0x21,
            0x84, 0xb8, 0xd7, 0x1c];

        let rr = mont::scalar_mult_base(&n.as_ref());
        assert_eq!(r.as_ref(), rr.as_ref());
    }

    #[bench]
    fn bench_scalar_mult_base(b: &mut Bencher) {
        let sk = mont::gen_key();
        b.iter(|| {
            let _ = mont::scalar_mult_base(&sk.read());
        })
    }

    #[bench]
    fn bench_scalar_mult(b: &mut Bencher) {
        let sk = mont::gen_key();
        let pk = mont::scalar_mult_base(&sk.read());
        let n: ProtBuf8 = ProtBuf::new_rand_os(SCALAR_SIZE);
        b.iter(|| {
            let _ = mont::scalar_mult(&n, &pk);
        })
    }
}
