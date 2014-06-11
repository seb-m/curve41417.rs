extern crate curve41417;

use curve41417::mont;

fn main() {
    let (pk1, sk1) = mont::keypair();
    let (pk2, sk2) = mont::keypair();

    let shared1 = mont::scalar_mult(&sk1, &pk2);
    let shared2 = mont::scalar_mult(&sk2, &pk1);

    assert!(shared1 == shared2);
}
