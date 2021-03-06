extern crate curve41417;
extern crate num;

use curve41417::ed::GroupElem;
use curve41417::mont;
use curve41417::sc::ScalarElem;
use num::FromPrimitive;


fn main () {
    // Note: most of the points illustrated in the code below may seem
    // a bit contrived without making much sense as it is. But the main
    // goal here is just to show few examples on how to use this lib.

    // Let's instanciate a new key pair in Montgomery's representation.
    let sk = mont::gen_key();
    let pkm = mont::scalar_mult_base(&sk.read());

    // `sk` is a secret key and is clamped so we can use it to compute its
    // corresponding public key in Edwards representation.
    let pke = GroupElem::base().scalar_mult(&sk.read());

    // In this case `pke` is not a packed value but still a group element
    // this is because we might want to apply others operations without
    // having to re-unpack it. Of course you could choose to pack it
    // explicitly simply by calling `pke.pack()`.

    // Moreover, at this point `pkm` and `pke` are expected to represent
    // the same point but in different representations. We can check that,
    // simply by converting `pke` to its Montgomery's representation.
    let pke_m = pke.pack_to_mont();
    assert_eq!(pkm, pke_m);

    // Some protocols need to perform basic operations directly on scalar
    // values modulo the base point's order. The `sc` module provides just
    // that. Let's use it and multiply `42` by `sk`.
    let sc_sk = ScalarElem::unpack(&sk.read()).unwrap();
    let sc_42 = FromPrimitive::from_u64(1).unwrap();
    let sc_sk42 = &sc_sk * &sc_42;

    // We can also pack the result and multiply it to its base point to see if
    // it matches `42 * pke`, as it should. In this case the `GroupElem` is
    // used to perform these operations as we don't want `42` to be clamped but
    // used as it is.
    let sk42 = sc_sk42.pack();
    let sh1 = GroupElem::base().scalar_mult(&sk42);
    let sh2 = pke.scalar_mult(&sc_42.pack());
    assert_eq!(sh1, sh2);
}
