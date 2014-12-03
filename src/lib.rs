//! [Curve41417](http://safecurves.cr.yp.to/) elliptic curve.
//!
//! This code is mainly inspired by [TweetNaCl](http://tweetnacl.cr.yp.to/)
//! and [Ed25519](http://ed25519.cr.yp.to/software.html).
//!
//! Souce code [repository](https://github.com/seb-m/curve41417.rs) on Github.
#![crate_name = "curve41417"]
#![experimental]  // Stability
#![doc(html_logo_url = "http://www.rust-lang.org/logos/rust-logo-128x128-blk.png",
       html_favicon_url = "http://www.rust-lang.org/favicon.ico",
       html_root_url = "http://doc.rust-lang.org/")]

#![feature(macro_rules)]
#![feature(slicing_syntax)]
#![feature(phase)]

#[cfg(test)] extern crate test;
#[cfg(test)] #[phase(plugin, link)] extern crate log;

extern crate serialize;
extern crate tars;

pub use common::{SCALAR_SIZE, BYTES_SIZE, Scalar};

mod common;
mod fe;
pub mod mont;
pub mod ed;
pub mod sc;
