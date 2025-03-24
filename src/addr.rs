use super::{Domain, Host, ParseAsciiHostError, ParseHostError};

use core::{
  net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr, SocketAddrV4, SocketAddrV6},
  str::FromStr,
};

/// An error which can be returned when parsing a [`HostAddr`].
#[derive(Debug, thiserror::Error)]
pub enum ParseHostAddrError {
  /// Returned if the provided str does not contains a valid host.
  #[error(transparent)]
  Host(#[from] ParseHostError),
  /// Returned if the provided str does not contains a valid port.
  #[error(transparent)]
  Port(#[from] core::num::ParseIntError),
}

/// An error which can be returned when parsing a [`HostAddr`].
#[derive(Debug, thiserror::Error)]
pub enum ParseAsciiHostAddrError {
  /// Returned if the provided str does not contains a valid host.
  #[error(transparent)]
  Host(#[from] ParseAsciiHostError),
  /// Returned if the provided str does not contains a valid port.
  #[error(transparent)]
  Port(#[from] core::num::ParseIntError),
}

/// A host address, which is consit of a [`Host`] and an optional port number.
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct HostAddr<S> {
  /// The host name
  pub(super) host: Host<S>,
  /// The port number
  pub(super) port: Option<u16>,
}

impl<S> core::fmt::Display for HostAddr<S>
where
  S: core::fmt::Display,
{
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    match self.port {
      Some(port) => write!(f, "{}:{}", self.host, port),
      None => write!(f, "{}", self.host),
    }
  }
}

impl<S> From<Domain<S>> for HostAddr<S> {
  fn from(domain: Domain<S>) -> Self {
    Self::from_domain(domain)
  }
}

impl<S> From<(Domain<S>, u16)> for HostAddr<S> {
  fn from((host, port): (Domain<S>, u16)) -> Self {
    Self::from_domain(host).with_port(port)
  }
}

impl<S> From<(u16, Domain<S>)> for HostAddr<S> {
  fn from((port, host): (u16, Domain<S>)) -> Self {
    Self::from_domain(host).with_port(port)
  }
}

impl<S> From<Host<S>> for HostAddr<S> {
  fn from(host: Host<S>) -> Self {
    Self::new(host)
  }
}

impl<S> From<(Host<S>, u16)> for HostAddr<S> {
  fn from((host, port): (Host<S>, u16)) -> Self {
    Self::new(host).with_port(port)
  }
}

impl<S> From<(u16, Host<S>)> for HostAddr<S> {
  fn from((port, host): (u16, Host<S>)) -> Self {
    Self::new(host).with_port(port)
  }
}

impl<S> From<(IpAddr, u16)> for HostAddr<S> {
  fn from((host, port): (IpAddr, u16)) -> Self {
    Self::from_ip_addr(host).with_port(port)
  }
}

impl<S> From<(u16, IpAddr)> for HostAddr<S> {
  fn from((port, host): (u16, IpAddr)) -> Self {
    Self::from_ip_addr(host).with_port(port)
  }
}

impl<S> From<(Ipv4Addr, u16)> for HostAddr<S> {
  fn from((host, port): (Ipv4Addr, u16)) -> Self {
    Self::from((IpAddr::V4(host), port))
  }
}

impl<S> From<(Ipv6Addr, u16)> for HostAddr<S> {
  fn from((host, port): (Ipv6Addr, u16)) -> Self {
    Self::from((port, IpAddr::V6(host)))
  }
}

impl<S> From<SocketAddr> for HostAddr<S> {
  fn from(addr: SocketAddr) -> Self {
    Self::from_sock_addr(addr)
  }
}

impl<S> From<SocketAddrV4> for HostAddr<S> {
  fn from(addr: SocketAddrV4) -> Self {
    Self::from_sock_addr(SocketAddr::V4(addr))
  }
}

impl<S> From<SocketAddrV6> for HostAddr<S> {
  fn from(addr: SocketAddrV6) -> Self {
    Self::from_sock_addr(SocketAddr::V6(addr))
  }
}

impl<S> From<IpAddr> for HostAddr<S> {
  fn from(ip: IpAddr) -> Self {
    Self::from_ip_addr(ip)
  }
}

impl<S> From<Ipv4Addr> for HostAddr<S> {
  fn from(ip: Ipv4Addr) -> Self {
    Self::from(IpAddr::V4(ip))
  }
}

impl<S> From<Ipv6Addr> for HostAddr<S> {
  fn from(ip: Ipv6Addr) -> Self {
    Self::from(IpAddr::V6(ip))
  }
}

impl<S> HostAddr<S> {
  /// Create a new host address
  ///
  /// ## Example
  ///
  /// ```rust
  /// use hostaddr::HostAddr;
  ///
  /// let host = HostAddr::<String>::new("example.com".parse().unwrap());
  /// println!("{}", host);
  /// ```
  #[inline]
  pub const fn new(host: Host<S>) -> Self {
    Self { host, port: None }
  }

  /// Create a new host address from a domain name
  ///
  /// ## Example
  ///
  /// ```rust
  /// use hostaddr::{HostAddr, Domain};
  ///
  /// let host = HostAddr::<String>::from_domain("example.com".parse().unwrap());
  /// println!("{}", host);
  /// ```
  #[inline]
  pub fn from_domain(domain: Domain<S>) -> Self {
    Self {
      host: Host::Domain(domain.0),
      port: None,
    }
  }

  /// Create a new host address from an IP address
  ///
  /// ## Example
  ///
  /// ```rust
  /// use hostaddr::HostAddr;
  ///
  /// let host = HostAddr::<String>::from_ip_addr("127.0.0.1".parse().unwrap());
  /// println!("{}", host);
  /// ```
  #[inline]
  pub const fn from_ip_addr(ip: IpAddr) -> Self {
    Self {
      host: Host::Ip(ip),
      port: None,
    }
  }

  /// Create a new host address from a `SocketAddr`
  ///
  /// ## Example
  ///
  /// ```rust
  /// use hostaddr::HostAddr;
  ///
  /// let host = HostAddr::<String>::from_sock_addr("127.0.0.1:8080".parse().unwrap());
  /// println!("{}", host);
  /// ```
  #[inline]
  pub const fn from_sock_addr(addr: SocketAddr) -> Self {
    Self {
      host: Host::Ip(addr.ip()),
      port: Some(addr.port()),
    }
  }

  /// Get the host name
  #[inline]
  pub const fn host(&self) -> &Host<S> {
    &self.host
  }

  /// Get the ip address
  #[inline]
  pub const fn ip(&self) -> Option<&IpAddr> {
    self.host.ip()
  }

  /// Get the port number
  #[inline]
  pub const fn port(&self) -> Option<u16> {
    self.port
  }

  /// Set the port number
  #[inline]
  pub const fn set_port(&mut self, port: u16) -> &mut Self {
    self.port = Some(port);
    self
  }

  /// Set the port number
  ///
  /// See also [`maybe_with_port`](Self::maybe_with_port).
  #[inline]
  pub const fn maybe_port(&mut self, port: Option<u16>) -> &mut Self {
    self.port = port;
    self
  }

  /// Set the port number
  ///
  /// See also [`maybe_port`](Self::maybe_port).
  #[inline]
  pub const fn maybe_with_port(mut self, port: Option<u16>) -> Self {
    self.port = port;
    self
  }

  /// Set the port number
  ///
  /// See also [`set_port`](Self::set_port).
  #[inline]
  pub const fn with_port(mut self, port: u16) -> Self {
    self.port = Some(port);
    self
  }

  /// Set the port number to `None`.
  ///
  /// See also [`maybe_port`](Self::maybe_port).
  #[inline]
  pub const fn clear_port(mut self) -> Self {
    self.port = None;
    self
  }

  /// Set the host name
  #[inline]
  pub fn set_host(&mut self, host: Host<S>) -> &mut Self {
    self.host = host;
    self
  }

  /// Set the host name
  #[inline]
  pub fn with_host<F>(mut self, host: Host<S>) -> Self {
    self.host = host;
    self
  }

  /// Returns `true` if the host is an IP address
  #[inline]
  pub const fn is_ip(&self) -> bool {
    self.host.is_ip()
  }

  /// Returns `true` if the host is an Ipv4 address
  #[inline]
  pub const fn is_ipv4(&self) -> bool {
    self.host.is_ipv4()
  }

  /// Returns `true` if the host is an Ipv6 address
  #[inline]
  pub const fn is_ipv6(&self) -> bool {
    self.host.is_ipv6()
  }

  /// Returns `true` if the host is a domain name
  #[inline]
  pub const fn is_domain(&self) -> bool {
    self.host.is_domain()
  }

  /// Converts from `&HostAddr<S>` to `HostAddr<&S>`.
  ///
  ///
  /// ## Example
  ///
  /// ```rust
  /// use std::sync::Arc;
  /// use hostaddr::HostAddr;
  ///
  /// let host: HostAddr<Arc<str>> = "example.com:8080".try_into().unwrap();
  /// assert_eq!("example.com", &**host.as_ref().host().unwrap_domain());
  /// ```
  #[inline]
  pub const fn as_ref(&self) -> HostAddr<&S> {
    HostAddr {
      host: self.host.as_ref(),
      port: self.port,
    }
  }

  /// Converts from `HostAddr<S>` (or `&HostAddr<S>`) to `HostAddr<&S::Target>`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use std::sync::Arc;
  /// use hostaddr::HostAddr;
  ///
  /// let host = "example.com:9090".parse::<HostAddr<Arc<str>>>().unwrap();
  /// assert_eq!("example.com", host.as_deref().host().unwrap_domain());
  /// ```
  #[inline]
  pub fn as_deref(&self) -> HostAddr<&S::Target>
  where
    S: core::ops::Deref,
  {
    HostAddr {
      host: self.host.as_deref(),
      port: self.port,
    }
  }

  /// Consumes the `HostAddr` and returns the host name and port number.
  #[inline]
  pub fn into_components(self) -> (Host<S>, Option<u16>) {
    let Self { host, port } = self;

    (host, port)
  }
}

impl<S> HostAddr<&S> {
  /// Maps an `HostAddr<&S>` to an `HostAddr<S>` by copying the contents of the
  /// host addr.
  #[inline]
  pub const fn copied(self) -> HostAddr<S>
  where
    S: Copy,
  {
    HostAddr {
      host: self.host.copied(),
      port: self.port,
    }
  }

  /// Maps an `HostAddr<&S>` to an `HostAddr<S>` by cloning the contents of the
  /// host addr.
  #[inline]
  pub fn cloned(self) -> HostAddr<S>
  where
    S: Clone,
  {
    HostAddr {
      host: self.host.cloned(),
      port: self.port,
    }
  }
}

macro_rules! try_from_str {
  ($convert:ident($s: ident)) => {{
    match try_parse_v6::<S>($s)? {
      Some(addr) => Ok(addr),
      None => {
        let mut parts = $s.splitn(2, ':');
        let host = parts
          .next()
          .ok_or(ParseHostAddrError::Host(ParseHostError(())))?
          .$convert()?;
        let port = match parts.next() {
          Some(port) => Some(port.parse().map_err(ParseHostAddrError::Port)?),
          None => None,
        };

        Ok(Self { host, port })
      }
    }
  }};
}

impl<'a> HostAddr<&'a str> {
  /// Parses a [`HostAddr`] name from `&str`.
  ///
  /// Unlike `HostAddr::try_from` or `HostAddr::from_str`, this method does not perform any percent decoding
  /// or punycode decoding. If the input is not ASCII, it will return an error.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use hostaddr::HostAddr;
  ///
  /// let host = HostAddr::try_from_ascii_str("example.com").unwrap();
  /// assert_eq!(host.unwrap_domain(), "example.com");
  ///
  /// // This will return an error because the domain is not ASCII.
  /// assert!(HostAddr::try_from_ascii_str("测试.中国").is_err());
  ///
  /// // Thie will not return an error, even though the human-readable domain is not ASCII.
  /// let host = HostAddr::try_from_ascii_str("xn--0zwm56d.xn--fiqs8s").unwrap();
  /// assert_eq!(host.unwrap_domain(), "xn--0zwm56d.xn--fiqs8s");
  /// ```
  #[inline]
  pub fn try_from_ascii_str(input: &'a str) -> Result<Self, ParseAsciiHostAddrError> {
    match try_parse_v6(input).map_err(|_| ParseAsciiHostAddrError::Host(ParseAsciiHostError(())))? {
      Some(addr) => Ok(addr),
      None => {
        let mut parts = input.splitn(2, ':');
        let host = Host::try_from_ascii_str(
          parts
            .next()
            .ok_or(ParseAsciiHostAddrError::Host(ParseAsciiHostError(())))?,
        )?;
        let port = match parts.next() {
          Some(port) => Some(port.parse().map_err(ParseAsciiHostAddrError::Port)?),
          None => None,
        };

        Ok(Self { host, port })
      }
    }
  }
}

impl<'a> HostAddr<&'a [u8]> {
  /// Parses a [`HostAddr`] from `&[u8]`.
  ///
  /// Unlike `HostAddr::try_from` or `HostAddr::from_str`, this method does not perform any percent decoding
  /// or punycode decoding. If the input is not ASCII, it will return an error.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use hostaddr::HostAddr;
  ///
  /// let host = HostAddr::try_from_ascii_bytes(b"example.com").unwrap();
  /// assert_eq!(host.unwrap_domain(), b"example.com");
  ///
  /// // This will return an error because the domain is not ASCII.
  /// assert!(HostAddr::try_from_ascii_bytes("测试.中国".as_bytes()).is_err());
  ///
  /// // Thie will not return an error, even though the human-readable domain is not ASCII.
  /// let host = HostAddr::try_from_ascii_bytes(b"xn--0zwm56d.xn--fiqs8s").unwrap();
  /// assert_eq!(host.unwrap_domain(), b"xn--0zwm56d.xn--fiqs8s");
  /// ```
  #[inline]
  pub fn try_from_ascii_bytes(input: &'a [u8]) -> Result<Self, ParseAsciiHostAddrError> {
    let input_str = simdutf8::basic::from_utf8(input).map_err(|_| ParseAsciiHostError(()))?;
    match try_parse_v6(input_str)
      .map_err(|_| ParseAsciiHostAddrError::Host(ParseAsciiHostError(())))?
    {
      Some(addr) => Ok(addr),
      None => {
        let mut parts = input_str.splitn(2, ':');
        let host = Host::try_from_ascii_bytes(
          parts
            .next()
            .map(|s| s.as_bytes())
            .ok_or(ParseAsciiHostAddrError::Host(ParseAsciiHostError(())))?,
        )?;
        let port = match parts.next() {
          Some(port) => Some(port.parse().map_err(ParseAsciiHostAddrError::Port)?),
          None => None,
        };

        Ok(Self { host, port })
      }
    }
  }
}

impl<S> FromStr for HostAddr<S>
where
  Domain<S>: FromStr,
{
  type Err = ParseHostAddrError;

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    try_from_str!(parse(s))
  }
}

impl<'a, S> TryFrom<&'a str> for HostAddr<S>
where
  Domain<S>: TryFrom<&'a str>,
{
  type Error = ParseHostAddrError;

  fn try_from(s: &'a str) -> Result<Self, Self::Error> {
    try_from_str!(try_into(s))
  }
}

fn try_parse_v6<S>(s: &str) -> Result<Option<HostAddr<S>>, ParseHostAddrError> {
  if s.starts_with("[") {
    // Ipv6 and no port
    if s.ends_with("]") {
      return s
        .parse()
        .map_err(|_| ParseHostAddrError::Host(ParseHostError(())))
        .map(|addr| Some(HostAddr::from_ip_addr(addr)));
    }

    // Ipv6 with port
    let mut parts = s.rsplitn(2, ':');

    let port = parts.next();
    let host = parts.next();

    match (host, port) {
      (Some(host), Some(_)) if host.ends_with("]") => {
        return s
          .parse()
          .map_err(|_| ParseHostAddrError::Host(ParseHostError(())))
          .map(|addr| Some(HostAddr::from_sock_addr(addr)));
      }
      _ => return Err(ParseHostAddrError::Host(ParseHostError(()))),
    }
  }

  Ok(None)
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_hostaddr_parsing() {
    let host: HostAddr<String> = "example.com".parse().unwrap();
    assert_eq!("example.com", host.as_ref().host().unwrap_domain());

    let host: HostAddr<String> = "example.com:8080".parse().unwrap();
    assert_eq!("example.com", host.as_ref().host().unwrap_domain());
    assert_eq!(Some(8080), host.port());

    let host: HostAddr<String> = "127.0.0.1:8080".parse().unwrap();
    assert_eq!(
      IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)),
      host.as_ref().host().unwrap_ip()
    );
    assert_eq!(Some(8080), host.port());

    let host: HostAddr<String> = "[::1]:8080".parse().unwrap();
    assert_eq!(
      IpAddr::V6(Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 1)),
      host.as_ref().host().unwrap_ip()
    );
    assert_eq!(Some(8080), host.port());
  }

  #[test]
  fn test_hostaddr_try_into() {
    let host: HostAddr<String> = "example.com".try_into().unwrap();
    assert_eq!("example.com", host.as_ref().host().unwrap_domain());

    let host: HostAddr<String> = "example.com:8080".try_into().unwrap();
    assert_eq!("example.com", host.as_ref().host().unwrap_domain());
    assert_eq!(Some(8080), host.port());

    let host: HostAddr<String> = "127.0.0.1:8080".try_into().unwrap();
    assert_eq!(
      IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)),
      host.as_ref().host().unwrap_ip()
    );
    assert_eq!(Some(8080), host.port());

    let host: HostAddr<String> = "[::1]:8080".try_into().unwrap();
    assert_eq!(
      IpAddr::V6(Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 1)),
      host.as_ref().host().unwrap_ip()
    );
    assert_eq!(Some(8080), host.port());
  }
}
