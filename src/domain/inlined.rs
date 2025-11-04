//! Stack-allocated buffer for storing validated domain names.
//!
//! This module provides the `Buffer` type, a fixed-size buffer designed for
//! storing domain names without heap allocation. It is ideal for `no_std` and
//! `no-alloc` environments.
//!
//! ## Design
//!
//! The `Buffer` type uses a 255-byte array to store domain names:
//! - 253 bytes for the domain name content (max DNS domain length)
//! - 1 byte for a trailing dot (for FQDNs)
//! - 1 byte to store the actual length
//!
//! This design allows `Buffer` to be used in const contexts and on the stack
//! without requiring any heap allocation.
//!
//! ## Usage
//!
//! The `Buffer` type is typically used with the `Domain<Buffer>` type:
//!
//! ```rust
//! use hostaddr::{Domain, Buffer};
//!
//! // Create a stack-allocated domain (no heap allocation)
//! let domain: Domain<Buffer> = Domain::try_from("example.com").unwrap();
//!
//! // Access as str or bytes
//! assert_eq!(domain.as_inner().as_str(), "example.com");
//! assert_eq!(domain.as_inner().as_bytes(), b"example.com");
//! ```
//!
//! ## Converting to Other Types
//!
//! `Buffer` can be converted to various string and byte types:
//!
//! ```rust
//! # #[cfg(any(feature = "std", feature = "alloc"))]
//! # {
//! use hostaddr::{Domain, Buffer};
//!
//! let domain: Domain<Buffer> = Domain::try_from("example.com").unwrap();
//!
//! // Convert to String
//! let s: String = domain.into_inner().into();
//!
//! // Convert to Vec<u8>
//! let domain: Domain<Buffer> = Domain::try_from("example.com").unwrap();
//! let v: Vec<u8> = domain.into_inner().into();
//! # }
//! ```

use core::borrow::Borrow;

/// An immutable buffer which contains a valid domain.
///
/// The internal storage is a `[u8; 255]` array with the following layout:
/// - bytes 0-253: domain name content
/// - byte 254: length of the domain name (0-254)
///
/// This fixed-size design allows the `Buffer` to be used in `no_std` and
/// `no-alloc` environments without requiring heap allocation.
///
/// ## Example
///
/// ```rust
/// use hostaddr::{Domain, Buffer};
///
/// let domain: Domain<Buffer> = Domain::try_from("example.com").unwrap();
/// assert_eq!(domain.as_inner().as_str(), "example.com");
/// ```
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, derive_more::Display)]
#[repr(transparent)]
#[display("{}", self.as_str())]
pub struct Buffer {
  /// 253 bytes for possible domain name, 1 byte for '.', 1 byte for length.
  buf: [u8; 255],
}

impl PartialOrd for Buffer {
  fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
    Some(self.cmp(other))
  }
}

impl Ord for Buffer {
  fn cmp(&self, other: &Self) -> core::cmp::Ordering {
    self.as_str().cmp(other.as_str())
  }
}

#[allow(unused)]
#[cfg(any(
  feature = "std",
  feature = "alloc",
  feature = "smol_str_0_3",
  feature = "triomphe_0_1",
  feature = "bytes_1",
  feature = "tinyvec_1",
  feature = "smallvec_1",
  feature = "bytes_1"
))]
macro_rules! impl_from_domain_buffer {
  ($($as:ident(
    $($into:ident -> $ty:ty), +$(,)?
  )), +$(,)?) => {
    $(
      $(
        impl_from_domain_buffer!($as -> $into -> $ty);
      )*
    )*
  };
  ($as:ident -> $into:ident -> $ty:ty) => {
    impl From<Buffer> for $ty {
      fn from(value: Buffer) -> Self {
        value.$as().$into()
      }
    }
  };
}

#[cfg(feature = "smol_str_0_3")]
impl_from_domain_buffer!(as_str -> into -> smol_str_0_3::SmolStr);
#[cfg(feature = "triomphe_0_1")]
impl_from_domain_buffer!(as_str -> into -> triomphe_0_1::Arc<str>);
#[cfg(feature = "triomphe_0_1")]
impl_from_domain_buffer!(as_bytes -> into -> triomphe_0_1::Arc<[u8]>);
#[cfg(feature = "bytes_1")]
const _: () = {
  use bytes_1::Bytes;

  impl From<Buffer> for Bytes {
    fn from(value: Buffer) -> Self {
      Bytes::copy_from_slice(value.as_bytes())
    }
  }
};
#[cfg(feature = "tinyvec_1")]
const _: () = {
  use tinyvec_1::TinyVec;

  impl<const N: usize> From<Buffer> for TinyVec<[u8; N]> {
    fn from(value: Buffer) -> Self {
      TinyVec::from(value.as_bytes())
    }
  }
};
#[cfg(feature = "smallvec_1")]
const _: () = {
  use smallvec_1::SmallVec;

  impl<const N: usize> From<Buffer> for SmallVec<[u8; N]> {
    fn from(value: Buffer) -> Self {
      SmallVec::from_slice(value.as_bytes())
    }
  }
};

#[cfg(any(feature = "std", feature = "alloc"))]
const _: () = {
  use std::{borrow::ToOwned, string::String, vec::Vec};

  impl_from_domain_buffer!(
    as_str(
      into -> String,
      into -> std::sync::Arc<str>,
      into -> std::boxed::Box<str>,
      into -> std::rc::Rc<str>,
    ),
    as_bytes(
      into -> Vec<u8>,
      into -> std::sync::Arc<[u8]>,
      into -> std::boxed::Box<[u8]>,
      into -> std::rc::Rc<[u8]>,
    ),
  );

  impl From<Buffer> for std::borrow::Cow<'_, str> {
    /// ```rust
    /// use hostaddr::{Buffer, Domain};
    ///
    /// let domain: Domain<Buffer> = "example.com".parse().unwrap();
    /// let str: std::borrow::Cow<'_, str> = domain.into_inner().into();
    /// ```
    fn from(value: Buffer) -> Self {
      std::borrow::Cow::Owned(value.as_str().to_owned())
    }
  }

  impl From<Buffer> for std::borrow::Cow<'_, [u8]> {
    /// ```rust
    /// use hostaddr::{Buffer, Domain};
    ///
    /// let domain: Domain<Buffer> = "example.com".parse().unwrap();
    /// let bytes: std::borrow::Cow<'_, [u8]> = domain.into_inner().into();
    /// ```
    fn from(value: Buffer) -> Self {
      std::borrow::Cow::Owned(value.as_bytes().to_owned())
    }
  }
};

impl<'a> From<&'a Buffer> for &'a str {
  /// ```rust
  /// # #[cfg(any(feature = "std", feature = "alloc"))]
  /// # {
  /// use hostaddr::{Buffer, Domain};
  ///
  /// let domain: Domain<Buffer> = "example.com".parse().unwrap();
  /// let str: &str = (&domain.into_inner()).into();
  /// # }
  /// ```
  fn from(value: &'a Buffer) -> Self {
    value.as_str()
  }
}

impl<'a> From<&'a Buffer> for &'a [u8] {
  /// ```rust
  /// # #[cfg(any(feature = "std", feature = "alloc"))]
  /// # {
  /// use hostaddr::{Buffer, Domain};
  ///
  /// let domain: Domain<Buffer> = "example.com".parse().unwrap();
  /// let bytes: &[u8] = (&domain.into_inner()).into();
  /// # }
  /// ```
  fn from(value: &'a Buffer) -> Self {
    value.as_bytes()
  }
}

impl Borrow<str> for Buffer {
  /// ```rust
  /// # #[cfg(any(feature = "std", feature = "alloc"))]
  /// # {
  /// use hostaddr::{Buffer, Domain};
  /// use std::borrow::Borrow;
  ///
  /// let domain: Domain<Buffer> = "example.com".parse().unwrap();
  /// let str: &str = domain.into_inner().borrow();
  /// # }
  /// ```
  #[inline]
  fn borrow(&self) -> &str {
    self.as_ref()
  }
}

impl AsRef<[u8]> for Buffer {
  /// ```rust
  /// # #[cfg(any(feature = "std", feature = "alloc"))]
  /// # {
  /// use hostaddr::{Buffer, Domain};
  ///
  /// let domain: Domain<Buffer> = "example.com".parse().unwrap();
  /// let bytes: &[u8] = domain.into_inner().as_ref();
  /// # }
  /// ```
  fn as_ref(&self) -> &[u8] {
    self.as_bytes()
  }
}

impl AsRef<str> for Buffer {
  /// ```rust
  /// # #[cfg(any(feature = "std", feature = "alloc"))]
  /// # {
  /// use hostaddr::{Buffer, Domain};
  ///
  /// let domain: Domain<Buffer> = "example.com".parse().unwrap();
  /// let str: &str = domain.into_inner().as_ref();
  /// # }
  /// ```
  fn as_ref(&self) -> &str {
    self.as_str()
  }
}

impl Buffer {
  #[inline]
  pub(super) const fn new() -> Self {
    Self { buf: [0; 255] }
  }

  /// Returns the domain as a `str`.
  #[inline]
  pub fn as_str(&self) -> &str {
    // SAFETY: The domain is guaranteed to be valid UTF-8.
    unsafe { core::str::from_utf8_unchecked(&self.buf[..self.len()]) }
  }

  /// Returns the domain as a `str`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// # #[cfg(any(feature = "std", feature = "alloc"))]
  /// # {
  /// use hostaddr::{Buffer, Domain};
  ///
  /// let domain: Domain<Buffer> = "example.com".parse().unwrap();
  /// assert_eq!("example.com", domain.into_inner().const_as_str());
  /// # }
  /// ```
  #[inline]
  pub const fn const_as_str(&self) -> &str {
    // SAFETY: The domain is guaranteed to be valid UTF-8.
    unsafe { core::str::from_utf8_unchecked(self.as_bytes()) }
  }

  /// Returns the domain as a `[u8]`
  #[inline]
  pub const fn as_bytes(&self) -> &[u8] {
    let len = self.len();
    self.buf.split_at(len).0
  }

  /// Push a `u8` to the buffer.
  #[inline]
  pub const fn push(&mut self, byte: u8) -> Result<(), u8> {
    let len = self.len();
    if len == 254 {
      return Err(byte);
    }
    self.buf[len] = byte;
    self.buf[254] += 1;
    Ok(())
  }

  #[inline]
  const fn len(&self) -> usize {
    *self.buf.last().unwrap() as usize
  }

  #[inline]
  pub(super) fn copy_from_slice(slice: &[u8]) -> Self {
    let len = slice.len();
    assert!(len <= 254, "domain name too long");

    let mut buf = Self::new();
    buf.buf[..len].copy_from_slice(slice);
    buf.buf[254] = len as u8;
    buf
  }

  #[inline]
  pub(super) fn copy_from_str(s: &str) -> Self {
    Self::copy_from_slice(s.as_bytes())
  }
}

impl core::fmt::Write for Buffer {
  fn write_str(&mut self, s: &str) -> core::fmt::Result {
    let len = s.len();
    let pos = self.len();
    if pos + len > 254 {
      return Err(core::fmt::Error);
    }
    self.buf[pos..pos + len].copy_from_slice(s.as_bytes());
    *self.buf.last_mut().unwrap() += len as u8;
    Ok(())
  }
}

#[cfg(feature = "serde")]
const _: () = {
  use core::fmt::Write;

  use either::Either;
  use serde::{Deserialize, Serialize};

  use super::Domain;

  impl Serialize for Buffer {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
      S: serde::Serializer,
    {
      if serializer.is_human_readable() {
        serializer.serialize_str(self.as_str())
      } else {
        serializer.serialize_bytes(self.as_bytes())
      }
    }
  }

  impl<'de> Deserialize<'de> for Buffer {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
      D: serde::Deserializer<'de>,
    {
      if deserializer.is_human_readable() {
        let s = <&str>::deserialize(deserializer)?;

        let res = Domain::try_from_str(s).map_err(serde::de::Error::custom)?;
        match res {
          Either::Left(d) => {
            let mut buf = Self::new();
            buf.write_str(d.0).map_err(serde::de::Error::custom)?;
            Ok(buf)
          }
          Either::Right(d) => Ok(d),
        }
      } else {
        let bytes = <&[u8]>::deserialize(deserializer)?;

        let res = Domain::try_from_bytes(bytes).map_err(serde::de::Error::custom)?;
        match res {
          Either::Left(d) => {
            let mut buf = Self::new();
            // SAFETY: Valid domains are guaranteed to be valid UTF-8.
            buf
              .write_str(unsafe { core::str::from_utf8_unchecked(d.0) })
              .map_err(serde::de::Error::custom)?;
            Ok(buf)
          }
          Either::Right(d) => Ok(d),
        }
      }
    }
  }
};

#[cfg(test)]
mod test {
  #[cfg(any(feature = "std", feature = "alloc", feature = "serde"))]
  #[test]
  fn test_ord() {
    use super::*;

    let a = Buffer::copy_from_str("a");
    let b = Buffer::copy_from_str("b");
    assert!(a < b);

    assert!(a.partial_cmp(&b) == Some(core::cmp::Ordering::Less));
  }
}
