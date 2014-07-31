//! [Curve41417](http://safecurves.cr.yp.to/) elliptic curve.
//!
//! This code is mainly inspired by [TweetNaCl](http://tweetnacl.cr.yp.to/)
//! and [Ed25519](http://ed25519.cr.yp.to/software.html).
#![crate_name = "curve41417"]
#![comment = "A pure-Rust Curve41417 implementation"]
#![license = "MIT/ASL2"]
#![experimental]  // Stability
#![doc(html_logo_url = "http://www.rust-lang.org/logos/rust-logo-128x128-blk.png",
       html_favicon_url = "http://www.rust-lang.org/favicon.ico",
       html_root_url = "http://doc.rust-lang.org/")]

#![feature(macro_rules)]
#![feature(unsafe_destructor)]
#![feature(default_type_params)]
#![feature(phase)]

#[cfg(test)] extern crate test;
#[cfg(test)] extern crate debug;
#[cfg(test)] #[phase(plugin, link)] extern crate log;

extern crate alloc;
extern crate libc;
extern crate serialize;

// Common modules
mod utils;
pub mod sbuf;

// Curve41417
pub mod bytes;
mod fe;
pub mod mont;
pub mod ed;
pub mod sc;
