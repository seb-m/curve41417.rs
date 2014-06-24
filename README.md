# Curve41417

## Description

A pure-[Rust](http://www.rust-lang.org/) implementation of [Curve41417](http://safecurves.cr.yp.to/).


## Building from source

* Build as library:

```
$ make
```

* Run tests, examples, benchmarks and build documentation:

```
$ make test
$ make examples  # Build examples from examples/
$ make bench
$ make doc  # Build documentation in doc/
```

## Example

Consider this basic example performing a Diffie-Hellman in Curve41417 Montgomery's representation:

```
extern crate curve41417;
use curve41417::mont;

let (pk1, sk1) = mont::keypair();
let (pk2, sk2) = mont::keypair();

let shared1 = mont::scalar_mult(&sk1, &pk2);
let shared2 = mont::scalar_mult(&sk2, &pk1);

assert!(shared1 == shared2);
```

For a more detailed example see [example.rs](examples/example.rs).


## Documentation

The generated documentation is available [here](http://seb.dbzteam.org/rust-curve41417/curve41417/).


## Notes

* This code is really experimental and its crypto operations are highly unoptimized, don't use it for anything serious. You know the rules, you've been warned.
* This code is mainly inspired by [TweetNaCl](http://tweetnacl.cr.yp.to/) and [Ed25519](http://ed25519.cr.yp.to/software.html).


## License

This code is distributed under the terms of both the MIT license and the Apache License (Version 2.0).
