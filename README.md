# Curve41417

## Description

A pure-[Rust](http://www.rust-lang.org/) implementation of [Curve41417](http://safecurves.cr.yp.to/). This code is experimental, don't use it for anything real.


## Building from source

Install Rust package manager [Cargo](https://github.com/rust-lang/cargo).


## Example

Consider this basic example performing a Diffie-Hellman in Curve41417 Montgomery's representation:

```rust
extern crate tars;
extern crate curve41417;

use tars::{BufAlloc, KeyAlloc, ProtBuf8, ProtKey8};
use curve41417::mont::{gen_key, scalar_mult_base, scalar_mult};

let sk1: ProtKey8<KeyAlloc> = gen_key();
let pk1: ProtBuf8<BufAlloc> = scalar_mult_base(&sk1.read());

let sk2: ProtKey8<KeyAlloc> = gen_key();
let pk2: ProtBuf8<BufAlloc> = scalar_mult_base(&sk2.read());

let shared1: ProtBuf8<BufAlloc> = scalar_mult(&sk1.read(), &pk2);
let shared2: ProtBuf8<BufAlloc> = scalar_mult(&sk2.read(), &pk1);

assert!(shared1 == shared2);
```

For a more detailed example see [curve41417_ops.rs](examples/curve41417_ops.rs).


## Documentation

The generated documentation is also available [here](http://seb.dbzteam.org/rs/curve41417/curve41417/).


## Notes

* This code is experimental and its crypto operations are highly unoptimized.
* This code is mainly inspired by [TweetNaCl](http://tweetnacl.cr.yp.to/) and [Ed25519](http://ed25519.cr.yp.to/software.html).


## License

This code is distributed under the terms of both the MIT license and the Apache License (Version 2.0).
