#![doc = include_str!("../README.md")]
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
#![deny(missing_docs)]

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

#[cfg(any(
  all(feature = "arbitrary", any(feature = "std", feature = "alloc")),
  all(test, any(feature = "std", feature = "alloc"))
))]
mod arbitrary_impl;
#[cfg(any(
  all(feature = "quickcheck", any(feature = "std", feature = "alloc")),
  all(test, any(feature = "std", feature = "alloc"))
))]
mod quickcheck_impl;

#[cfg(all(test, any(feature = "std", feature = "alloc")))]
mod test;
