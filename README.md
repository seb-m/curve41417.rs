# Curve41417

## Description

A pure-[Rust](http://www.rust-lang.org/) implementation of [Curve41417](http://safecurves.cr.yp.to/). This code is experimental, don't use it for anything real.


## Building from source

Install Rust package manager [Cargo](https://github.com/rust-lang/cargo).

* Build as library:

```
$ cargo build
```

* Run tests, examples, benchmarks and build documentation:

```
$ cargo test  # Run tests and build examples under target/test/
$ cargo bench
$ cargo doc   # Build documentation under target/doc/
```


## Example

Consider this basic example performing a Diffie-Hellman in Curve41417 Montgomery's representation:

```
extern crate curve41417;
use curve41417::bytes::{MontPoint, Scalar};
use curve41417::mont;

let (pk1, sk1): (MontPoint, Scalar) = mont::keypair();
let (pk2, sk2) = mont::keypair();

let shared1 = mont::scalar_mult(&sk1, &pk2);
let shared2 = mont::scalar_mult(&sk2, &pk1);

assert!(shared1 == shared2);
```

For a more detailed example see [curve41417_ops.rs](examples/curve41417_ops.rs).


## Documentation

The generated documentation is also available [here](http://seb.dbzteam.org/curve41417.rs/curve41417/).


## Notes

* This code is experimental and its crypto operations are highly unoptimized.
* This code is mainly inspired by [TweetNaCl](http://tweetnacl.cr.yp.to/) and [Ed25519](http://ed25519.cr.yp.to/software.html).


## License

This code is distributed under the terms of both the MIT license and the Apache License (Version 2.0).
