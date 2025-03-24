use core::{
  net::{IpAddr, Ipv4Addr, Ipv6Addr},
  str::FromStr,
};

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
  derive_more::IsVariant,
  derive_more::Unwrap,
)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "snake_case"))]
#[unwrap(ref, ref_mut)]
pub enum Host<S> {
  /// A DNS domain name
  Domain(S),
  /// An IP address
  Ip(IpAddr),
}

impl<'a> Host<&'a str> {
  /// Parses an ASCII [`Host`] from `&str`.
  ///
  /// Unlike `Host::try_from` or `Host::from_str`, this method does not perform any percent decoding
  /// or punycode decoding. If the input is not ASCII, it will return an error.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use hostaddr::Host;
  ///
  /// let host = Host::try_from_ascii_str("example.com").unwrap();
  /// assert_eq!(host.unwrap_domain(), "example.com");
  ///
  /// // This will return an error because the domain is not ASCII.
  /// assert!(Host::try_from_ascii_str("测试.中国").is_err());
  ///
  /// // Thie will not return an error, even though the human-readable domain is not ASCII.
  /// let host = Host::try_from_ascii_str("xn--0zwm56d.xn--fiqs8s").unwrap();
  /// assert_eq!(host.unwrap_domain(), "xn--0zwm56d.xn--fiqs8s");
  /// ```
  #[inline]
  pub fn try_from_ascii_str(input: &'a str) -> Result<Self, ParseAsciiHostError> {
    if let Ok(ip) = input.parse() {
      return Ok(Host::Ip(ip));
    }

    Domain::try_from_ascii_str(input)
      .map(|d| Host::Domain(d.0))
      .map_err(|_| ParseAsciiHostError(()))
  }
}

impl<'a> Host<&'a [u8]> {
  /// Parses an ASCII [`Host`]  from `&[u8]`.
  ///
  /// Unlike `Host::try_from` or `Host::from_str`, this method does not perform any percent decoding
  /// or punycode decoding. If the input is not ASCII, it will return an error.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use hostaddr::Host;
  ///
  /// let host = Host::try_from_ascii_bytes(b"example.com").unwrap();
  /// assert_eq!(host.unwrap_domain(), b"example.com");
  ///
  /// // This will return an error because the domain is not ASCII.
  /// assert!(Host::try_from_ascii_bytes("测试.中国".as_bytes()).is_err());
  ///
  /// // Thie will not return an error, even though the human-readable domain is not ASCII.
  /// let host = Host::try_from_ascii_bytes(b"xn--0zwm56d.xn--fiqs8s").unwrap();
  /// assert_eq!(host.unwrap_domain(), b"xn--0zwm56d.xn--fiqs8s");
  /// ```
  #[inline]
  pub fn try_from_ascii_bytes(input: &'a [u8]) -> Result<Self, ParseAsciiHostError> {
    let input_str = simdutf8::basic::from_utf8(input).map_err(|_| ParseAsciiHostError(()))?;
    if let Ok(ip) = input_str.parse() {
      return Ok(Host::Ip(ip));
    }

    Domain::try_from_ascii_bytes(input)
      .map(|d| Host::Domain(d.0))
      .map_err(|_| ParseAsciiHostError(()))
  }
}

impl<S> From<Domain<S>> for Host<S> {
  /// ```rust
  /// use hostaddr::{Domain, Host};
  ///
  /// let domain: Domain<String> = "example.com".parse().unwrap();
  /// let host: Host<String> = domain.into();
  /// ```
  fn from(value: Domain<S>) -> Self {
    Self::Domain(value.0)
  }
}

impl<S> From<IpAddr> for Host<S> {
  /// ```rust
  /// use hostaddr::Host;
  /// use std::net::IpAddr;
  ///
  /// let ip: IpAddr = "127.0.0.1".parse().unwrap();
  /// let host: Host<String> = ip.into();
  /// ```
  fn from(value: IpAddr) -> Self {
    Self::from_ip(value)
  }
}

impl<S> From<Ipv4Addr> for Host<S> {
  /// ```rust
  /// use hostaddr::Host;
  /// use std::net::Ipv4Addr;
  ///
  /// let ip: Ipv4Addr = "127.0.0.1".parse().unwrap();
  /// let host: Host<String> = ip.into();
  /// ```
  fn from(value: Ipv4Addr) -> Self {
    Self::from(IpAddr::V4(value))
  }
}

impl<S> From<Ipv6Addr> for Host<S> {
  /// ```rust
  /// use hostaddr::Host;
  /// use std::net::Ipv6Addr;
  ///
  /// let ip: Ipv6Addr = "::1".parse().unwrap();
  /// let host: Host<String> = ip.into();
  /// ```
  fn from(value: Ipv6Addr) -> Self {
    Self::from(IpAddr::V6(value))
  }
}

impl<S> Host<S> {
  /// Creates a new `Host` from an IP address.
  #[inline]
  pub const fn from_ip(ip: IpAddr) -> Self {
    Self::Ip(ip)
  }

  /// Returns `true` if the host is an Ipv4 address.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use hostaddr::Host;
  ///
  /// let host: Host<&str> = Host::from_ip("127.0.0.1".parse().unwrap());
  /// assert!(host.is_ipv4());
  /// ```
  #[inline]
  pub const fn is_ipv4(&self) -> bool {
    matches!(self, Host::Ip(IpAddr::V4(_)))
  }

  /// Returns `true` if the host is an Ipv6 address.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use hostaddr::Host;
  ///
  /// let host: Host<&str> = Host::from_ip("::1".parse().unwrap());
  /// assert!(host.is_ipv6());
  /// ```
  #[inline]
  pub const fn is_ipv6(&self) -> bool {
    matches!(self, Host::Ip(IpAddr::V6(_)))
  }

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
  /// assert_eq!("example.com", &**host.as_ref().unwrap_domain());
  /// ```
  #[inline]
  pub const fn as_ref(&self) -> Host<&S> {
    match self {
      Host::Domain(domain) => Host::Domain(domain),
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
  /// assert_eq!("example.com", host.as_deref().unwrap_domain());
  /// ```
  #[inline]
  pub fn as_deref(&self) -> Host<&S::Target>
  where
    S: core::ops::Deref,
  {
    match self {
      Host::Domain(domain) => Host::Domain(core::ops::Deref::deref(domain)),
      Host::Ip(ip) => Host::Ip(*ip),
    }
  }

  /// Returns `Some(ip)` if the host is an IP address.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use hostaddr::Host;
  /// use std::net::IpAddr;
  ///
  /// let host: Host<String> = "127.0.0.1".parse().unwrap();
  /// assert_eq!(Some("127.0.0.1".parse().unwrap()), host.ip().copied());
  ///
  /// let host: Host<String> = "example.com".parse().unwrap();
  /// assert!(host.ip().is_none());
  /// ```
  #[inline]
  pub const fn ip(&self) -> Option<&IpAddr> {
    match self {
      Host::Ip(ip) => Some(ip),
      _ => None,
    }
  }

  /// Returns `Some(domain)` if the host is a domain name.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use hostaddr::Host;
  ///
  /// let host: Host<String> = "example.com".parse().unwrap();
  /// assert_eq!(Some("example.com".to_string()), host.domain().cloned());
  ///
  /// let host: Host<String> = "127.0.0.1".parse().unwrap();
  /// assert!(host.domain().is_none());
  /// ```
  #[inline]
  pub const fn domain(&self) -> Option<&S> {
    match self {
      Host::Domain(domain) => Some(domain),
      _ => None,
    }
  }
}

impl<S> Host<&S> {
  /// Maps an `Host<&S>` to an `Host<S>` by copying the contents of the
  /// host.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use hostaddr::{Host, Buffer};
  /// use std::net::IpAddr;
  ///
  /// let host: Host<Buffer> = Host::try_from("example.com").unwrap();
  /// assert_eq!("example.com", host.as_ref().copied().unwrap_domain().as_str());
  ///
  /// let host: Host<Buffer> = "127.0.0.1".parse().unwrap();
  /// assert_eq!("127.0.0.1".parse::<IpAddr>().unwrap(), host.as_ref().copied().unwrap_ip());
  /// ```
  #[inline]
  pub const fn copied(self) -> Host<S>
  where
    S: Copy,
  {
    match self {
      Self::Domain(domain) => Host::Domain(*domain),
      Self::Ip(ip) => Host::Ip(ip),
    }
  }

  /// Maps an `Host<&S>` to an `Host<S>` by cloning the contents of the
  /// host.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use hostaddr::Host;
  /// use std::net::IpAddr;
  ///
  /// let host: Host<String> = "example.com".parse().unwrap();
  /// assert_eq!("example.com", host.as_ref().cloned().unwrap_domain().as_str());
  ///
  /// let host: Host<String> = "127.0.0.1".parse().unwrap();
  /// assert_eq!("127.0.0.1".parse::<IpAddr>().unwrap(), host.as_ref().cloned().unwrap_ip());
  /// ```
  #[inline]
  pub fn cloned(self) -> Host<S>
  where
    S: Clone,
  {
    match self {
      Self::Domain(domain) => Host::Domain(domain.clone()),
      Self::Ip(ip) => Host::Ip(ip),
    }
  }
}

macro_rules! try_from_str {
  ($convert:ident($s:ident)) => {{
    if let Ok(ip) = $s.parse() {
      return Ok(Host::Ip(ip));
    }

    $s.$convert()
      .map(|d: Domain<S>| Host::Domain(d.0))
      .map_err(|_| ParseHostError(()))
  }};
}

impl<S> FromStr for Host<S>
where
  Domain<S>: FromStr,
{
  type Err = ParseHostError;

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    try_from_str!(parse(s))
  }
}

impl<'a, S> TryFrom<&'a str> for Host<S>
where
  Domain<S>: TryFrom<&'a str>,
{
  type Error = ParseHostError;

  fn try_from(s: &'a str) -> Result<Self, Self::Error> {
    try_from_str!(try_into(s))
  }
}

/// An error which can be returned when parsing an ASCII [`Host`].
#[derive(Debug, Clone, Copy, thiserror::Error)]
#[error("{}", self.as_str())]
pub struct ParseAsciiHostError(pub(super) ());

impl ParseAsciiHostError {
  /// Returns the error message.
  #[inline]
  pub const fn as_str(&self) -> &'static str {
    "invalid ASCII host"
  }
}

/// An error which can be returned when parsing a [`Host`].
#[derive(Debug, Clone, thiserror::Error)]
#[error("{}", self.as_str())]
pub struct ParseHostError(pub(super) ());

impl ParseHostError {
  /// Returns the error message.
  #[inline]
  pub const fn as_str(&self) -> &'static str {
    "invalid host"
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use std::string::String;

  #[test]
  fn negative_from_str() {
    let err = "@a".parse::<Host<String>>().unwrap_err();
    assert_eq!(err.as_str(), "invalid host");
  }

  #[test]
  fn negative_try_from_str() {
    let err = Host::<String>::try_from("@a").unwrap_err();
    assert_eq!(err.as_str(), "invalid host");
  }

  #[test]
  fn ip_from_ascii_str() {
    let host = Host::try_from_ascii_str("127.0.0.1").unwrap();
    assert!(host.is_ipv4());

    let err = Host::try_from_ascii_str("@a").unwrap_err();
    assert_eq!(err.as_str(), "invalid ASCII host");
  }

  #[test]
  fn ip_from_ascii_bytes() {
    let host = Host::try_from_ascii_bytes(b"127.0.0.1").unwrap();
    assert!(host.is_ipv4());

    let err = Host::try_from_ascii_str("@a").unwrap_err();
    assert_eq!(err.as_str(), "invalid ASCII host");
  }
}
