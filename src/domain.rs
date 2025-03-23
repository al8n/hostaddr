use either::Either;
use idna::{
  uts46::{verify_dns_length, ErrorPolicy, Hyphens, ProcessingSuccess, Uts46},
  AsciiDenyList,
};
use memchr::Memchr;
use simdutf8::basic::from_utf8;

use core::borrow::Borrow;
use std::{borrow::Cow, string::String, vec::Vec};

pub use inlined::DomainBuffer;

mod inlined;

/// The provided input could not be parsed because
/// it is not a syntactically-valid DNS Domain.
#[derive(Debug, Clone, Copy, thiserror::Error)]
#[error("invalid domain")]
pub struct ParseDomainError(pub(super) ());

impl ParseDomainError {
  /// Returns the error message.
  #[inline]
  pub const fn as_str(&self) -> &'static str {
    "invalid domain"
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
  #[inline]
  fn borrow(&self) -> &S {
    &self.0
  }
}

impl<S> Domain<S> {
  /// Parses a domain name from `&[u8]`.
  #[inline]
  pub fn try_from_bytes(input: S) -> Result<Either<Self, DomainBuffer>, ParseDomainError>
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
      let mut domain_buf = DomainBuffer::new();
      for byte in input {
        domain_buf.push(byte).map_err(|_| ParseDomainError(()))?;
      }

      let input = domain_buf.as_bytes();
      if input.is_ascii() {
        return verify_ascii_domain(input).map(|_| Either::Right(domain_buf));
      }

      let mut sinker = DomainBuffer::new();
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

    let mut sinker = DomainBuffer::new();
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
  #[inline]
  pub fn try_from_str(input: S) -> Result<Either<Self, DomainBuffer>, ParseDomainError>
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
        type Err = ParseDomainError;

        fn from_str(s: &str) -> Result<Self, Self::Err> {
          Domain::try_from_str(s).map(|res| match res {
            Either::Left(d) => Self($from(d)),
            Either::Right(d) => Self(d.into()),
          })
        }
      }

      impl<'a> TryFrom<&'a str> for Domain<$ty> {
        type Error = ParseDomainError;

        fn try_from(value: &'a str) -> Result<Self, Self::Error> {
          core::str::FromStr::from_str(value)
        }
      }
    )*
  };
  (@bytes $($from:expr => $ty:ty), +$(,)?) => {
    $(
      impl<'a> TryFrom<&'a [u8]> for Domain<$ty> {
        type Error = ParseDomainError;

        fn try_from(value: &'a [u8]) -> Result<Self, Self::Error> {
          Domain::try_from_bytes(value).map(|res| match res {
            Either::Left(d) => Self(($from)(d)),
            Either::Right(d) => Self(d.into()),
          })
        }
      }
    )*
  };
  (@owned $($try_from:ident($as:ident, $ty:ty)), +$(,)?) => {
    $(
      impl TryFrom<$ty> for Domain<$ty> {
        type Error = ParseDomainError;

        fn try_from(value: $ty) -> Result<Self, Self::Error> {
          Ok(match Domain::$try_from(value.$as())? {
            Either::Left(_) => Self(value),
            Either::Right(d) => Self(d.into()),
          })
        }
      }

      impl<'a> TryFrom<&'a $ty> for Domain<$ty> {
        type Error = ParseDomainError;

        fn try_from(value: &'a $ty) -> Result<Self, Self::Error> {
          Ok(match Domain::$try_from(value.$as())? {
            Either::Left(_) => Self(value.clone()),
            Either::Right(d) => Self(d.into()),
          })
        }
      }
    )*
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
