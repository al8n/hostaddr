use core::{net::IpAddr, str::FromStr};

pub use derive_more::TryUnwrapError;

use super::Domain;

/// The host name
#[derive(
  Clone,
  Copy,
  Debug,
  Eq,
  PartialEq,
  PartialOrd,
  Ord,
  Hash,
  derive_more::Display,
  derive_more::From,
  derive_more::IsVariant,
  derive_more::TryUnwrap,
  derive_more::Unwrap,
)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "snake_case"))]
#[unwrap(ref, ref_mut)]
#[try_unwrap(ref, ref_mut)]
pub enum Host<S> {
  /// A DNS domain name
  Domain(Domain<S>),
  /// An IP address
  Ip(IpAddr),
}

impl<S> Host<S> {
  /// Converts from `&Host<S>` to `Host<&S>`.
  ///
  ///
  /// ## Example
  ///
  /// ```rust
  /// use std::sync::Arc;
  /// use hostaddr::Host;
  ///
  /// let host = "example.com".parse::<Host<Arc<str>>>().unwrap();
  /// assert_eq!("example.com", &**host.as_ref().unwrap_domain().into_inner());
  /// ```
  #[inline]
  pub const fn as_ref(&self) -> Host<&S> {
    match self {
      Host::Domain(domain) => Host::Domain(domain.as_ref()),
      Host::Ip(ip) => Host::Ip(*ip),
    }
  }

  /// Converts from `Host<S>` (or `&Host<S>`) to `Host<&S::Target>`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use std::sync::Arc;
  /// use hostaddr::Host;
  ///
  /// let host: Host<Arc<str>> = "example.com".try_into().unwrap();
  /// let host_ref = host.as_deref();
  /// assert_eq!("example.com", host_ref.unwrap_domain().into_inner());
  /// ```
  #[inline]
  pub fn as_deref(&self) -> Host<&S::Target>
  where
    S: core::ops::Deref,
  {
    match self {
      Host::Domain(domain) => Host::Domain(domain.as_deref()),
      Host::Ip(ip) => Host::Ip(*ip),
    }
  }
}

impl<S> FromStr for Host<S>
where
  Domain<S>: FromStr,
{
  type Err = ParseHostError;

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    if let Ok(ip) = s.parse() {
      return Ok(Host::Ip(ip));
    }

    s.parse().map(Host::Domain).map_err(|_| ParseHostError(()))
  }
}

impl<'a, S> TryFrom<&'a str> for Host<S>
where
  Domain<S>: TryFrom<&'a str>,
{
  type Error = ParseHostError;

  fn try_from(s: &'a str) -> Result<Self, Self::Error> {
    if let Ok(ip) = s.parse() {
      return Ok(Host::Ip(ip));
    }

    s.try_into()
      .map(Host::Domain)
      .map_err(|_| ParseHostError(()))
  }
}

/// An error which can be returned when parsing a [`HostAddr`].
#[derive(Debug, Clone, thiserror::Error)]
#[error("invalid host")]
pub struct ParseHostError(pub(super) ());

impl ParseHostError {
  /// Returns the error message.
  #[inline]
  pub const fn as_str(&self) -> &'static str {
    "invalid host"
  }
}
