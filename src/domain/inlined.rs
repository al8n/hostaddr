use core::borrow::Borrow;

use std::{string::String, vec::Vec};

use simdutf8::basic::from_utf8;

/// An immutable buffer which contains a valid domain.
///
/// The internal is a `[u8; 255]` array.
#[derive(Debug, Clone, PartialEq, Eq, Hash, derive_more::Display)]
#[repr(transparent)]
#[display("{}", self.as_str())]
pub struct DomainBuffer {
  /// 253 bytes for possible domain name, 1 byte for '.', 1 byte for length.
  buf: [u8; 255],
}

impl PartialOrd for DomainBuffer {
  fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
    Some(self.cmp(other))
  }
}

impl Ord for DomainBuffer {
  fn cmp(&self, other: &Self) -> core::cmp::Ordering {
    self.as_str().cmp(other.as_str())
  }
}

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
    impl From<DomainBuffer> for $ty {
      fn from(value: DomainBuffer) -> Self {
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

impl From<DomainBuffer> for std::borrow::Cow<'_, str> {
  fn from(value: DomainBuffer) -> Self {
    std::borrow::Cow::Owned(value.as_str().to_owned())
  }
}

impl From<DomainBuffer> for std::borrow::Cow<'_, [u8]> {
  fn from(value: DomainBuffer) -> Self {
    std::borrow::Cow::Owned(value.as_bytes().to_owned())
  }
}

impl<'a> From<&'a DomainBuffer> for &'a str {
  fn from(value: &'a DomainBuffer) -> Self {
    value.as_str()
  }
}

impl<'a> From<&'a DomainBuffer> for &'a [u8] {
  fn from(value: &'a DomainBuffer) -> Self {
    value.as_bytes()
  }
}

impl Borrow<str> for DomainBuffer {
  #[inline]
  fn borrow(&self) -> &str {
    self.as_ref()
  }
}

impl AsRef<[u8]> for DomainBuffer {
  fn as_ref(&self) -> &[u8] {
    self.as_bytes()
  }
}

impl AsRef<str> for DomainBuffer {
  fn as_ref(&self) -> &str {
    self.as_str()
  }
}

impl DomainBuffer {
  #[inline]
  pub(super) const fn new() -> Self {
    Self { buf: [0; 255] }
  }

  /// Returns the domain as a `str`.
  #[inline]
  pub fn as_str(&self) -> &str {
    from_utf8(&self.buf[..self.len()]).expect("valid UTF-8")
  }

  /// Returns the domain as a `str`.
  #[inline]
  pub const fn const_as_str(&self) -> &str {
    match core::str::from_utf8(self.as_bytes()) {
      Ok(s) => s,
      Err(_) => panic!("invalid UTF-8"),
    }
  }

  /// Returns the domian as a `[u8]`
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
    self.buf[len + 1] += 1;
    Ok(())
  }

  #[inline]
  const fn len(&self) -> usize {
    *self.buf.last().unwrap() as usize
  }
}

impl core::fmt::Write for DomainBuffer {
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

  impl Serialize for DomainBuffer {
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

  impl<'de> Deserialize<'de> for DomainBuffer {
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
            buf
              .write_str(from_utf8(d.0).map_err(serde::de::Error::custom)?)
              .map_err(serde::de::Error::custom)?;
            Ok(buf)
          }
          Either::Right(d) => Ok(d),
        }
      }
    }
  }
};
