use either::Either;
use idna::{
  uts46::{verify_dns_length, ErrorPolicy, Hyphens, ProcessingSuccess, Uts46},
  AsciiDenyList,
};
use memchr::Memchr;
use simdutf8::basic::from_utf8;

use core::borrow::Borrow;
use std::{
  borrow::Cow,
  string::{String, ToString},
  vec::Vec,
};

pub use inlined::Buffer;

mod inlined;

/// The provided input could not be parsed because
/// it is not a syntactically-valid DNS Domain.
#[derive(Debug, Clone, Copy, thiserror::Error)]
#[error("{}", self.as_str())]
pub struct ParseDomainError(pub(super) ());

impl ParseDomainError {
  /// Returns the error message.
  #[inline]
  pub const fn as_str(&self) -> &'static str {
    "invalid domain"
  }
}

/// The provided input could not be parsed because
/// it is not an ASCII syntactically-valid DNS Domain.
#[derive(Debug, Clone, Copy, thiserror::Error)]
#[error("{}", self.as_str())]
pub struct ParseAsciiDomainError(pub(super) ());

impl ParseAsciiDomainError {
  /// Returns the error message.
  #[inline]
  pub const fn as_str(&self) -> &'static str {
    "invalid ASCII domain"
  }
}

/// A DNS domain name, as `.` dot-separated labels.
/// Non-ASCII labels are encoded in punycode per IDNA if this is the host of a special URL,
/// or percent encoded for non-special URLs.
///
/// ## Note
/// In this implementation, a fully-qualified domain name (FQDN) is valid. This means that
/// the domain name can end with a `.` dot.
///
/// e.g.
/// - `example.com.` is a valid domain name, because it is a FQDN.
/// - A single `.` dot is a valid domain name, because it is root domain.
///
///
/// ## Example
///
/// ```rust
/// use std::{sync::Arc, str::FromStr};
///
/// use hostaddr::Domain;
///
/// let domain = Domain::<String>::from_str("example.com").unwrap();
/// assert_eq!(domain.as_inner(), "example.com");
///
/// let domain = Domain::<String>::from_str("пример.испытание").unwrap();
/// assert_eq!(domain.as_inner(), "xn--e1afmkfd.xn--80akhbyknj4f");
///
/// let domain = Domain::<Arc<str>>::from_str("测试.中国").unwrap();
/// assert_eq!(domain.as_inner().as_ref(), "xn--0zwm56d.xn--fiqs8s");
///
/// let domain = Domain::<Arc<[u8]>>::try_from("test.com".as_bytes()).unwrap();
/// assert_eq!(domain.as_inner().as_ref(), b"test.com");
/// ```
#[derive(
  Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, derive_more::Display, derive_more::AsRef,
)]
#[repr(transparent)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct Domain<S>(pub(super) S);

impl<S> Domain<S> {
  /// Returns the reference to the inner `S`.
  #[inline]
  pub const fn as_inner(&self) -> &S {
    &self.0
  }

  /// Returns the inner `S`.
  #[inline]
  pub fn into_inner(self) -> S {
    self.0
  }

  /// Converts from `&Domain<S>` to `Domain<&S>`.
  #[inline]
  pub const fn as_ref(&self) -> Domain<&S> {
    Domain(&self.0)
  }

  /// Converts from `Domain<S>` (or `&Domain<S>`) to `Domain<&S::Target>`.
  #[inline]
  pub fn as_deref(&self) -> Domain<&S::Target>
  where
    S: core::ops::Deref,
  {
    Domain(self.0.deref())
  }
}

impl<S> Borrow<S> for Domain<S> {
  /// ```rust
  /// use hostaddr::Domain;
  /// use std::borrow::Borrow;
  ///
  /// let domain: Domain<&[u8]> = Domain::try_from_ascii_bytes(b"example.com").unwrap();
  /// let bytes: &&[u8] = domain.borrow();
  ///
  /// assert_eq!(bytes, b"example.com");
  /// ```
  #[inline]
  fn borrow(&self) -> &S {
    &self.0
  }
}

impl<S> AsRef<str> for Domain<S>
where
  S: AsRef<str>,
{
  /// ```rust
  /// use hostaddr::Domain;
  ///
  /// let domain: Domain<&str> = Domain::try_from_ascii_str("example.com").unwrap();
  /// let s: &str = AsRef::as_ref(&domain);
  ///
  /// assert_eq!(s, "example.com");
  /// ```
  #[inline]
  fn as_ref(&self) -> &str {
    self.0.as_ref()
  }
}

impl<S> AsRef<[u8]> for Domain<S>
where
  S: AsRef<[u8]>,
{
  /// ```rust
  /// use hostaddr::Domain;
  /// use std::borrow::Borrow;
  ///
  /// let domain: Domain<&[u8]> = Domain::try_from_ascii_bytes(b"example.com").unwrap();
  /// let bytes: &[u8] = AsRef::as_ref(&domain);
  ///
  /// assert_eq!(bytes, b"example.com");
  /// ```
  #[inline]
  fn as_ref(&self) -> &[u8] {
    self.0.as_ref()
  }
}

impl<S> Domain<&S> {
  /// Maps an `Domain<&S>` to an `Domain<S>` by copying the contents of the
  /// domain.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use hostaddr::{Domain, Buffer};
  ///
  /// let domain: Domain<Buffer> = Domain::try_from("example.com").unwrap();
  /// assert_eq!("example.com", domain.as_ref().copied().as_inner().as_str());
  /// ```
  #[inline]
  pub const fn copied(self) -> Domain<S>
  where
    S: Copy,
  {
    Domain(*self.0)
  }

  /// Maps an `Domain<&S>` to an `Domain<S>` by cloning the contents of the
  /// domain.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use hostaddr::Domain;
  ///
  /// let domain: Domain<String> = "example.com".parse().unwrap();
  /// assert_eq!("example.com", domain.as_ref().cloned().as_inner().as_str());
  /// ```
  #[inline]
  pub fn cloned(self) -> Domain<S>
  where
    S: Clone,
  {
    Domain(self.0.clone())
  }
}

impl<'a> Domain<&'a str> {
  /// Parses a domain name from `&str`.
  ///
  /// Unlike `Domain::try_from_str`, this method does not perform any percent decoding
  /// or punycode decoding. If the input is not ASCII, it will return an error.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use hostaddr::Domain;
  ///
  /// let domain = Domain::try_from_ascii_str("example.com").unwrap();
  /// assert_eq!(domain.into_inner(), "example.com");
  ///
  /// // This will return an error because the domain is not ASCII.
  /// assert!(Domain::try_from_ascii_str("测试.中国").is_err());
  ///
  /// // Thie will not return an error, even though the human-readable domain is not ASCII.
  /// let domain = Domain::try_from_ascii_str("xn--0zwm56d.xn--fiqs8s").unwrap();
  /// assert_eq!(domain.into_inner(), "xn--0zwm56d.xn--fiqs8s");
  /// ```
  #[inline]
  pub const fn try_from_ascii_str(input: &'a str) -> Result<Self, ParseAsciiDomainError> {
    if !input.is_ascii() {
      return Err(ParseAsciiDomainError(()));
    }

    match verify_ascii_domain(input.as_bytes()) {
      Ok(_) => Ok(Self(input)),
      Err(_) => Err(ParseAsciiDomainError(())),
    }
  }
}

impl<'a> Domain<&'a [u8]> {
  /// Parses a domain name from `&[u8]`.
  ///
  /// Unlike `Domain::try_from_bytes`, this method does not perform any percent decoding
  /// or punycode decoding. If the input is not ASCII, it will return an error.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use hostaddr::Domain;
  ///
  /// let domain = Domain::try_from_ascii_bytes(b"example.com").unwrap();
  /// assert_eq!(domain.into_inner(), b"example.com");
  ///
  /// // This will return an error because the domain is not ASCII.
  /// assert!(Domain::try_from_ascii_bytes("测试.中国".as_bytes()).is_err());
  ///
  /// // Thie will not return an error, even though the human-readable domain is not ASCII.
  /// let domain = Domain::try_from_ascii_bytes(b"xn--0zwm56d.xn--fiqs8s").unwrap();
  /// assert_eq!(domain.into_inner(), b"xn--0zwm56d.xn--fiqs8s");
  /// ```
  #[inline]
  pub const fn try_from_ascii_bytes(input: &'a [u8]) -> Result<Self, ParseAsciiDomainError> {
    if !input.is_ascii() {
      return Err(ParseAsciiDomainError(()));
    }

    match verify_ascii_domain(input) {
      Ok(_) => Ok(Self(input)),
      Err(_) => Err(ParseAsciiDomainError(())),
    }
  }
}

impl<S> Domain<S> {
  /// Parses a domain name from `&[u8]`.
  ///
  /// If you can make sure the input is ASCII and not percent encoded,
  /// then [`Domain::try_from_ascii_bytes`] should be used instead.
  ///
  /// ## Note
  ///
  /// 1. If the given input is encoded in percent encoding, it will be decoded.
  /// 2. If the given input is not ASCII, it will be converted to ASCII using punycode.
  /// 3. Otherwise, the input will be returned as is.
  ///
  /// If the `1.` & `2.` happen, the result will be returned as a `Either::Right(Buffer)`.
  ///
  /// If the input is not a valid domain name, this method will return an error.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use hostaddr::Domain;
  ///
  /// let domain = Domain::try_from_bytes(b"example.com").unwrap();
  /// assert_eq!(domain.unwrap_left().into_inner(), b"example.com");
  ///
  /// let domain = Domain::try_from_bytes("测试.中国".as_bytes()).unwrap();
  /// assert_eq!(domain.unwrap_right().as_bytes(), b"xn--0zwm56d.xn--fiqs8s");
  ///
  /// let domain = Domain::try_from_bytes(b"example%2Ecom").unwrap();
  /// assert_eq!(domain.unwrap_right().as_bytes(), b"example.com");
  ///
  /// let domain = Domain::try_from_bytes("测试%2E中国".as_bytes()).unwrap();
  /// assert_eq!(domain.unwrap_right().as_bytes(), b"xn--0zwm56d.xn--fiqs8s");
  /// ```
  #[inline]
  pub fn try_from_bytes(input: S) -> Result<Either<Self, Buffer>, ParseDomainError>
  where
    S: AsRef<[u8]>,
  {
    macro_rules! validate_length {
      ($buf:expr) => {{
        if !verify_dns_length($buf, true) {
          return Err(ParseDomainError(()));
        }
      }};
    }

    let domain = input.as_ref();
    // We have percent encoded bytes, so we need to decode them.
    if Memchr::new(b'%', domain).next().is_some() {
      let input = percent_encoding::percent_decode(domain);
      let mut domain_buf = Buffer::new();
      for byte in input {
        domain_buf.push(byte).map_err(|_| ParseDomainError(()))?;
      }

      let input = domain_buf.as_bytes();
      if input.is_ascii() {
        return verify_ascii_domain(input).map(|_| Either::Right(domain_buf));
      }

      let mut sinker = Buffer::new();
      let buf = match domain_to_ascii(input, &mut sinker)? {
        Either::Left(_) => domain_buf,
        Either::Right(_) => sinker,
      };

      validate_length!(buf.as_str());
      return Ok(Either::Right(buf));
    }

    if domain.is_ascii() {
      return verify_ascii_domain(domain).map(|_| Either::Left(Self(input)));
    }

    let mut sinker = Buffer::new();
    Ok(match domain_to_ascii(domain, &mut sinker)? {
      Either::Left(_) => {
        validate_length!(from_utf8(domain).map_err(|_| ParseDomainError(()))?);
        Either::Left(Self(input))
      }
      Either::Right(_) => {
        validate_length!(sinker.as_str());
        Either::Right(sinker)
      }
    })
  }

  /// Parses a domain name from `&str`.
  ///
  /// If you can make sure the input is ASCII and not percent encoded,
  /// then [`Domain::try_from_ascii_str`] should be used instead.
  ///
  /// ## Note
  ///
  /// 1. If the given input is encoded in percent encoding, it will be decoded.
  /// 2. If the given input is not ASCII, it will be converted to ASCII using punycode.
  /// 3. Otherwise, the input will be returned as is.
  ///
  /// If the `1.` & `2.` happen, the result will be returned as a `Either::Right(Buffer)`.
  ///
  /// If the input is not a valid domain name, this method will return an error.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use hostaddr::Domain;
  ///
  /// let domain = Domain::try_from_str("example.com").unwrap();
  /// assert_eq!(domain.unwrap_left().into_inner(), "example.com");
  ///
  /// let domain = Domain::try_from_str("测试.中国").unwrap();
  /// assert_eq!(domain.unwrap_right().as_str(), "xn--0zwm56d.xn--fiqs8s");
  ///
  /// let domain = Domain::try_from_str("example%2Ecom").unwrap();
  /// assert_eq!(domain.unwrap_right().as_str(), "example.com");
  ///
  /// let domain = Domain::try_from_str("测试%2E中国").unwrap();
  /// assert_eq!(domain.unwrap_right().as_str(), "xn--0zwm56d.xn--fiqs8s");
  /// ```
  #[inline]
  pub fn try_from_str(input: S) -> Result<Either<Self, Buffer>, ParseDomainError>
  where
    S: AsRef<str>,
  {
    let domain = input.as_ref();
    Ok(
      match Domain::try_from_bytes(domain.as_bytes()).map_err(|_| ParseDomainError(()))? {
        Either::Left(_) => Either::Left(Self(input)),
        Either::Right(d) => Either::Right(d),
      },
    )
  }
}

macro_rules! impl_try_from {
  (@str $($from:expr => $ty:ty), +$(,)?) => {
    $(
      impl core::str::FromStr for Domain<$ty> {
        impl_try_from!(@from_str_impl $from);
      }

      impl<'a> TryFrom<&'a str> for Domain<$ty> {
        impl_try_from!(@try_from_str_impl $from);
      }
    )*
  };
  (@str_const_n $($from:expr => $ty:ty), +$(,)?) => {
    $(
      impl<const N: usize> core::str::FromStr for Domain<$ty> {
        impl_try_from!(@from_str_impl $from);
      }

      impl<'a, const N: usize> TryFrom<&'a str> for Domain<$ty> {
        impl_try_from!(@try_from_str_impl $from);
      }
    )*
  };
  (@from_str_impl $from:expr) => {
    type Err = ParseDomainError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
      Domain::try_from_str(s).map(|res| match res {
        Either::Left(d) => Self($from(d)),
        Either::Right(d) => Self(d.into()),
      })
    }
  };
  (@try_from_str_impl $($from:expr), +$(,)?) => {
    type Error = ParseDomainError;

    fn try_from(value: &'a str) -> Result<Self, Self::Error> {
      core::str::FromStr::from_str(value)
    }
  };
  (@bytes $($from:expr => $ty:ty), +$(,)?) => {
    $(
      impl<'a> TryFrom<&'a [u8]> for Domain<$ty> {
        impl_try_from!(@bytes_impl $from);
      }
    )*
  };
  (@bytes_const_n $($from:expr => $ty:ty), +$(,)?) => {
    $(
      impl<'a, const N: usize> TryFrom<&'a [u8]> for Domain<$ty> {
        impl_try_from!(@bytes_impl $from);
      }
    )*
  };
  (@bytes_impl $($from:expr), +$(,)?) => {
    $(
      type Error = ParseDomainError;

      fn try_from(value: &'a [u8]) -> Result<Self, Self::Error> {
        Domain::try_from_bytes(value).map(|res| match res {
          Either::Left(d) => Self(($from)(d)),
          Either::Right(d) => Self(d.into()),
        })
      }
    )*
  };
  (@owned $($try_from:ident($as:ident, $ty:ty)), +$(,)?) => {
    $(
      impl TryFrom<$ty> for Domain<$ty> {
        impl_try_from!(@owned_try_from_impl $try_from($as, $ty));
      }

      impl<'a> TryFrom<&'a $ty> for Domain<$ty> {
        impl_try_from!(@owned_try_from_ref_impl $try_from($as, $ty));
      }
    )*
  };
  (@owned_const_n $($try_from:ident($as:ident, $ty:ty)), +$(,)?) => {
    $(
      impl<const N: usize> TryFrom<$ty> for Domain<$ty> {
        impl_try_from!(@owned_try_from_impl $try_from($as, $ty));
      }

      impl<'a, const N: usize> TryFrom<&'a $ty> for Domain<$ty> {
        impl_try_from!(@owned_try_from_ref_impl $try_from($as, $ty));
      }
    )*
  };
  (@owned_try_from_impl $try_from:ident($as:ident, $ty:ty)) => {
    type Error = ParseDomainError;

    fn try_from(value: $ty) -> Result<Self, Self::Error> {
      Ok(match Domain::$try_from(value.$as())? {
        Either::Left(_) => Self(value.clone()),
        Either::Right(d) => Self(d.into()),
      })
    }
  };
  (@owned_try_from_ref_impl $try_from:ident($as:ident, $ty:ty)) => {
    type Error = ParseDomainError;

    fn try_from(value: &'a $ty) -> Result<Self, Self::Error> {
      Ok(match Domain::$try_from(value.$as())? {
        Either::Left(_) => Self(value.clone()),
        Either::Right(d) => Self(d.into()),
      })
    }
  };
}

#[cfg(feature = "smol_str_0_3")]
const _: () = {
  use smol_str_0_3::SmolStr;

  impl_try_from!(@str
    |d: Domain<_>| SmolStr::from(d.0) => SmolStr,
  );
  impl_try_from!(@bytes
    |d: Domain<_>| SmolStr::from(from_utf8(d.0).expect("domain is ASCII")) => SmolStr,
  );
  impl_try_from!(@owned try_from_str(as_str, SmolStr));
};

#[cfg(feature = "triomphe_0_1")]
const _: () = {
  use triomphe_0_1::Arc;

  impl_try_from!(@str
    |d: Domain<_>| Arc::<str>::from(d.0) => Arc<str>,
    |d: Domain<&str>| Arc::<[u8]>::from(d.0.as_bytes()) => Arc<[u8]>,
  );
  impl_try_from!(@bytes
    |d: Domain<_>| Arc::from(d.0) => Arc<[u8]>,
    |d: Domain<&[u8]>| Arc::from(from_utf8(d.0).expect("doamain is ASCII")) => Arc<str>,
  );
  impl_try_from!(@owned try_from_str(as_ref, Arc<str>), try_from_bytes(as_ref, Arc<[u8]>));
};

#[cfg(feature = "bytes_1")]
const _: () = {
  use bytes_1::Bytes;

  impl_try_from!(@str
    |d: Domain<&str>| Bytes::copy_from_slice(d.0.as_bytes()) => Bytes,
  );
  impl_try_from!(@bytes
    |d: Domain<_>| Bytes::copy_from_slice(d.0) => Bytes,
  );
  impl_try_from!(@owned try_from_bytes(as_ref, Bytes));
};

#[cfg(feature = "tinyvec_1")]
const _: () = {
  use tinyvec_1::TinyVec;

  impl_try_from!(@str_const_n
    |d: Domain<&str>| TinyVec::from(d.0.as_bytes()) => TinyVec<[u8; N]>,
  );
  impl_try_from!(@bytes_const_n
    |d: Domain<_>| TinyVec::from(d.0) => TinyVec<[u8; N]>,
  );
  impl_try_from!(
    @owned_const_n try_from_bytes(as_ref, TinyVec<[u8; N]>),
  );
};

#[cfg(feature = "smallvec_1")]
const _: () = {
  use smallvec_1::SmallVec;

  impl_try_from!(@str_const_n
    |d: Domain<&str>| SmallVec::from_slice(d.0.as_bytes()) => SmallVec<[u8; N]>,
  );
  impl_try_from!(@bytes_const_n
    |d: Domain<_>| SmallVec::from_slice(d.0) => SmallVec<[u8; N]>,
  );
  impl_try_from!(@owned_const_n try_from_bytes(as_ref, SmallVec<[u8; N]>));
};

impl<'a> TryFrom<&'a str> for Domain<Cow<'a, str>> {
  type Error = ParseDomainError;

  fn try_from(value: &'a str) -> Result<Self, Self::Error> {
    Domain::try_from_str(value).map(|res| match res {
      Either::Left(d) => Self(Cow::Borrowed(d.0)),
      Either::Right(d) => Self(d.into()),
    })
  }
}

impl<'a> TryFrom<&'a [u8]> for Domain<Cow<'a, [u8]>> {
  type Error = ParseDomainError;

  fn try_from(value: &'a [u8]) -> Result<Self, Self::Error> {
    Domain::try_from_bytes(value).map(|res| match res {
      Either::Left(d) => Self(Cow::Borrowed(d.0)),
      Either::Right(d) => Self(d.into()),
    })
  }
}

impl_try_from!(
  @str
  |d: Domain<_>| String::from(d.0) => String,
  |d: Domain<_>| std::sync::Arc::from(d.0) => std::sync::Arc<str>,
  |d: Domain<_>| std::boxed::Box::from(d.0) => std::boxed::Box<str>,
  |d: Domain<_>| std::rc::Rc::from(d.0) => std::rc::Rc<str>,
  |d: Domain<&str>| d.0.into() => Vec<u8>,
  |d: Domain<&str>| std::sync::Arc::from(d.0.as_bytes()) => std::sync::Arc<[u8]>,
  |d: Domain<&str>| std::boxed::Box::from(d.0.as_bytes()) => std::boxed::Box<[u8]>,
  |d: Domain<&str>| std::rc::Rc::from(d.0.as_bytes()) => std::rc::Rc<[u8]>,
  |d: Domain<&str>| {
    Buffer::copy_from_str(d.0)
  } => Buffer,
);

impl_try_from!(
  @bytes
  |d: Domain<_>| from_utf8(d.0).expect("domain is ASCII").to_string() => String,
  |d: Domain<_>| std::sync::Arc::from(from_utf8(d.0).expect("domain is ASCII")) => std::sync::Arc<str>,
  |d: Domain<_>| std::boxed::Box::from(from_utf8(d.0).expect("domain is ASCII")) => std::boxed::Box<str>,
  |d: Domain<_>| std::rc::Rc::from(from_utf8(d.0).expect("domain is ASCII")) => std::rc::Rc<str>,
  |d: Domain<&[u8]>| d.0.to_vec() => Vec<u8>,
  |d: Domain<_>| std::sync::Arc::from(d.0) => std::sync::Arc<[u8]>,
  |d: Domain<_>| std::boxed::Box::from(d.0) => std::boxed::Box<[u8]>,
  |d: Domain<_>| std::rc::Rc::from(d.0) => std::rc::Rc<[u8]>,
  |d: Domain<&[u8]>| Buffer::copy_from_slice(d.0) => Buffer,
);

impl_try_from!(
  @owned
  try_from_str(as_str, String),
  try_from_str(as_ref, std::sync::Arc<str>),
  try_from_str(as_ref, std::boxed::Box<str>),
  try_from_str(as_ref, std::rc::Rc<str>),
  try_from_bytes(as_slice, Vec<u8>),
  try_from_bytes(as_ref, std::sync::Arc<[u8]>),
  try_from_bytes(as_ref, std::boxed::Box<[u8]>),
  try_from_bytes(as_ref, std::rc::Rc<[u8]>),
);

fn domain_to_ascii<S>(domain: &[u8], mut sinker: S) -> Result<Either<&str, S>, ParseDomainError>
where
  S: core::fmt::Write,
{
  let uts46 = Uts46::new();
  let result = uts46.process(
    domain,
    AsciiDenyList::URL,
    Hyphens::Allow,
    ErrorPolicy::FailFast,
    |_, _, _| false, // Force ToASCII processing
    &mut sinker,
    None,
  );
  Ok(match result {
    Ok(res) => match res {
      ProcessingSuccess::WroteToSink => Either::Right(sinker),
      ProcessingSuccess::Passthrough => {
        Either::Left(from_utf8(domain).map_err(|_| ParseDomainError(()))?)
      }
    },
    Err(_) => return Err(ParseDomainError(())),
  })
}

/// Verifies that the input is a valid ASCII domain name.
///
/// This function cannot be used to verify non-ASCII domain names.
const fn verify_ascii_domain(input: &[u8]) -> Result<(), ParseDomainError> {
  enum State {
    Start,
    Next,
    NumericOnly { len: usize },
    NextAfterNumericOnly,
    Subsequent { len: usize },
    Hyphen { len: usize },
  }

  use State::*;

  let mut state = Start;

  /// "Labels must be 63 characters or less."
  const MAX_LABEL_LENGTH: usize = 63;

  /// https://devblogs.microsoft.com/oldnewthing/20120412-00/?p=7873
  const MAX_NAME_LENGTH: usize = 253;

  let len = input.len();
  if len == 0 {
    return Err(ParseDomainError(()));
  }

  if len == MAX_NAME_LENGTH + 1 {
    let Some(b'.') = input.last() else {
      return Err(ParseDomainError(()));
    };
  }

  if input[0] == b'.' && len == 1 {
    return Ok(());
  }

  let mut i = 0;
  while i < len {
    let ch = input[i];
    state = match (state, ch) {
      (Start | Next | NextAfterNumericOnly | Hyphen { .. }, b'.') => {
        return Err(ParseDomainError(()))
      }
      (Subsequent { .. }, b'.') => Next,
      (NumericOnly { .. }, b'.') => NextAfterNumericOnly,
      (Subsequent { len } | NumericOnly { len } | Hyphen { len }, _) if len >= MAX_LABEL_LENGTH => {
        return Err(ParseDomainError(()));
      }
      (Start | Next | NextAfterNumericOnly, b'0'..=b'9') => NumericOnly { len: 1 },
      (NumericOnly { len }, b'0'..=b'9') => NumericOnly { len: len + 1 },
      (Start | Next | NextAfterNumericOnly, b'a'..=b'z' | b'A'..=b'Z' | b'_') => {
        Subsequent { len: 1 }
      }
      (Subsequent { len } | NumericOnly { len } | Hyphen { len }, b'-') => Hyphen { len: len + 1 },
      (
        Subsequent { len } | NumericOnly { len } | Hyphen { len },
        b'a'..=b'z' | b'A'..=b'Z' | b'_' | b'0'..=b'9',
      ) => Subsequent { len: len + 1 },
      _ => return Err(ParseDomainError(())),
    };
    i += 1;
  }

  if matches!(
    state,
    Start | Hyphen { .. } | NumericOnly { .. } | NextAfterNumericOnly
  ) {
    return Err(ParseDomainError(()));
  }

  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn negative_try_from_ascii_bytes() {
    let err = Domain::<&[u8]>::try_from_ascii_bytes("测试.中国".as_bytes()).unwrap_err();
    assert_eq!(err.as_str(), "invalid ASCII domain");
    let err = Domain::<&[u8]>::try_from_ascii_bytes("@example.com".as_bytes()).unwrap_err();
    assert_eq!(err.as_str(), "invalid ASCII domain");
  }

  #[test]
  fn negative_try_from_ascii_str() {
    let err = Domain::<&str>::try_from_ascii_str("测试.中国").unwrap_err();
    assert_eq!(err.as_str(), "invalid ASCII domain");
    let err = Domain::<&str>::try_from_ascii_str("@example.com").unwrap_err();
    assert_eq!(err.as_str(), "invalid ASCII domain");
  }
}
