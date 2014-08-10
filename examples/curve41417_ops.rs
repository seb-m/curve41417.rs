#![feature(default_type_params)]

extern crate curve41417;

use curve41417::bytes::{B416, Bytes, Scalar};
use curve41417::ed::GroupElem;
use curve41417::mont;
use curve41417::sc::ScalarElem;
use curve41417::sbuf::DefaultAllocator;


fn main () {
    // Disclaimer: most of the points illustrated in the code below may
    // seem a bit contrived and doesn't make much sense as it is, but the
    // main goal here is to show a wide array of what's possible with this
    // library.

    // Let's instanciate a new key pair in Montgomery's representation.
    // `DefaultAllocator` represents a memory allocator used to allocate
    // memory buffers for this variable and for internal temporary buffers
    // used in crypto operations. This type parameter is optional and
    // defaults to `DefaultAllocator` when not provided.
    let (pkm, sk) = mont::keypair::<DefaultAllocator>();

    // `sk` is a generic scalar and is clamped so we can use it as is to
    // compute the corresponding public key in Edwards representation.
    let pke: GroupElem<DefaultAllocator> = GroupElem::base().scalar_mult(&sk);

    // In this case `pke` is not a packed value but still a group element
    // this is because we might want to apply others operations without
    // having to re-unpack it. Of course you could choose to pack it
    // explicitly simply by calling `pke.pack()`.

    // Moreover, at this point `pkm` and `pke` are expected to represent
    // the same point but in different representations. We can check that,
    // simply by converting `pke` to its Montgomery's representation.
    let pke_m = pke.to_mont();
    println!("[pkm == pke_m]: {} == {}", pkm, pke_m);
    assert!(pkm == pke_m);

    // To prevent common mistakes input arguments for main crypto operations
    // must explicitly be wrapped in `Scalar`, `MontPoint` or `EdPoint`.
    // Likewise results are often wrapped in these structs when needed.

    // Let's illustrate it by instanciating a new scalar.
    let mut b2: B416<DefaultAllocator> = Bytes::new_rand();
    b2.clamp_41417();

    // Transform `b2` to an explicit scalar value and multiply DH-style to
    // `pkm`.
    let sk2 = Scalar(b2);
    let shared = sk2 * pkm;
    println!("shared: {}", shared);

    // To conclude, some protocols need to perform basic operations directly
    // on scalar vakues modulo the base point's order. The `sc` module
    // provides just that. Let's multiply `42` by `sk`.
    let sc_sk: ScalarElem<DefaultAllocator> = ScalarElem::unpack(&sk).unwrap();
    let sc_42: ScalarElem<DefaultAllocator> =
        FromPrimitive::from_u64(42).unwrap();
    let sc_sk42: ScalarElem<DefaultAllocator> = sc_sk * sc_42;

    // We can also pack the result and multiply it to its base point to see if
    // it matches `42 * pke`, it should. In this case the `GroupElem` is used
    // to perform these operations as we don't want `42` to be clamped but
    // taken as it is.
    let sk42 = sc_sk42.pack();
    let sh1 = GroupElem::base().scalar_mult(&sk42);
    let sh2 = pke.scalar_mult(&sc_42.pack());
    assert!(sh1 == sh2);
}
