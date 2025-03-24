#![doc = include_str!("../README.md")]
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
#![deny(missing_docs)]

#[cfg(not(any(feature = "alloc", feature = "std")))]
compile_error!("`hostaddr` requires either the `alloc` or `std` feature to be enabled.");

#[cfg(all(not(feature = "std"), feature = "alloc"))]
extern crate alloc as std;

#[cfg(feature = "std")]
extern crate std;

pub use addr::*;
pub use domain::*;
pub use host::*;

mod addr;
mod domain;
mod host;

#[cfg(any(feature = "arbitrary", test))]
mod arbitrary_impl;
#[cfg(any(feature = "quickcheck", test))]
mod quickcheck_impl;

#[cfg(test)]
mod test;
