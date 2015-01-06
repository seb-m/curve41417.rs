# Curve41417

## Description

A pure-[Rust](http://www.rust-lang.org/) implementation of [Curve41417](http://safecurves.cr.yp.to/). This code is experimental, don't use it for anything real.

[![Build Status](https://travis-ci.org/seb-m/curve41417.rs.svg?branch=master)](https://travis-ci.org/seb-m/curve41417.rs)


## Documentation

The generated documentation is available [here](http://seb.dbzteam.org/rs/curve41417/curve41417/).


## Example

This basic example performs a Diffie-Hellman in Curve41417 Montgomery's representation:

```rust
extern crate curve41417;

use curve41417::mont::{gen_key, scalar_mult_base, scalar_mult};

let sk1 = gen_key();
let pk1 = scalar_mult_base(&sk1.read());

let sk2 = gen_key();
let pk2 = scalar_mult_base(&sk2.read());

let shared1 = scalar_mult(&sk1.read(), &pk2);
let shared2 = scalar_mult(&sk2.read(), &pk1);

assert_eq!(shared1, shared2);
```

For another example see [curve41417_ops.rs](examples/curve41417_ops.rs).


## Notes

* This code is experimental and its crypto operations are highly unoptimized.
* This code is mainly inspired by [TweetNaCl](http://tweetnacl.cr.yp.to/) and [Ed25519](http://ed25519.cr.yp.to/software.html).


## License

This code is distributed under the terms of both the MIT license and the Apache License (Version 2.0).
