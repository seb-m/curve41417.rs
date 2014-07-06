//! Pure-Rust [Curve41417](http://safecurves.cr.yp.to/) implementation.
#![crate_name = "curve41417"]
#![crate_type = "lib"]
#![crate_type = "dylib"]
#![crate_type = "rlib"]

#![comment = "A pure-Rust Curve41417 implementation"]
#![license = "MIT/ASL2"]

#![doc(html_logo_url = "http://www.rust-lang.org/logos/rust-logo-128x128-blk.png",
       html_favicon_url = "http://www.rust-lang.org/favicon.ico",
       html_root_url = "http://doc.rust-lang.org/")]

#![feature(macro_rules)]
#![feature(unsafe_destructor)]
#![feature(default_type_params)]

#![allow(dead_code)]

#[cfg(test)] extern crate debug;
extern crate alloc;
extern crate libc;
extern crate serialize;

mod utils;
pub mod sbuf; // fixme: pub ?
pub mod bytes;
mod fe;
pub mod mont;
pub mod ed;
pub mod sc;
pub mod chacha20; //fixme
