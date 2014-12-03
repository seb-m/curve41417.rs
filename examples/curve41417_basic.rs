extern crate tars;
extern crate curve41417;

use tars::{BufAlloc, KeyAlloc, ProtBuf8, ProtKey8};
use curve41417::mont::{gen_key, scalar_mult_base, scalar_mult};


fn main() {
    let sk1: ProtKey8<KeyAlloc> = gen_key();
    let pk1: ProtBuf8<BufAlloc> = scalar_mult_base(&sk1.read());

    let sk2: ProtKey8<KeyAlloc> = gen_key();
    let pk2: ProtBuf8<BufAlloc> = scalar_mult_base(&sk2.read());

    let shared1: ProtBuf8<BufAlloc> = scalar_mult(&sk1.read(), &pk2);
    let shared2: ProtBuf8<BufAlloc> = scalar_mult(&sk2.read(), &pk1);

    assert!(shared1 == shared2);
}
