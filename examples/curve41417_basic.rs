extern crate curve41417;

use curve41417::mont::{gen_key, scalar_mult_base, scalar_mult};


fn main() {
    let sk1 = gen_key();
    let pk1 = scalar_mult_base(&sk1.read());

    let sk2 = gen_key();
    let pk2 = scalar_mult_base(&sk2.read());

    let shared1 = scalar_mult(&sk1.read(), &pk2);
    let shared2 = scalar_mult(&sk2.read(), &pk1);

    assert!(shared1 == shared2);
}
