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

use core::{
  net::{IpAddr, SocketAddr, SocketAddrV4, SocketAddrV6},
  str::FromStr,
};

pub use domain::*;
pub use host::*;

mod domain;
mod host;

/// An error which can be returned when parsing a [`HostAddr`].
#[derive(Debug, thiserror::Error)]
pub enum ParseHostAddrError {
  /// Returned if the provided str is missing port.
  #[error("address is missing port")]
  PortNotFound,
  /// Returned if the provided str does not contains a valid host.
  #[error(transparent)]
  Host(#[from] ParseHostError),
  /// Returned if the provided str does not contains a valid port.
  #[error("invalid port: {0}")]
  Port(#[from] core::num::ParseIntError),
}

/// A host address, which is consit of a [`Host`] and an optional port number.
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct HostAddr<S> {
  /// The host name
  host: Host<S>,
  /// The port number
  port: u16,
}

impl<S> From<(Domain<S>, u16)> for HostAddr<S> {
  fn from((host, port): (Domain<S>, u16)) -> Self {
    Self {
      host: Host::Domain(host),
      port,
    }
  }
}

impl<S> From<(u16, Domain<S>)> for HostAddr<S> {
  fn from((port, host): (u16, Domain<S>)) -> Self {
    Self {
      host: Host::Domain(host),
      port,
    }
  }
}

impl<S> From<(IpAddr, u16)> for HostAddr<S> {
  fn from((host, port): (IpAddr, u16)) -> Self {
    Self {
      host: Host::Ip(host),
      port,
    }
  }
}

impl<S> From<SocketAddr> for HostAddr<S> {
  fn from(addr: SocketAddr) -> Self {
    Self {
      host: Host::Ip(addr.ip()),
      port: addr.port(),
    }
  }
}

impl<S> From<SocketAddrV4> for HostAddr<S> {
  fn from(addr: SocketAddrV4) -> Self {
    Self {
      host: Host::Ip(IpAddr::V4(*addr.ip())),
      port: addr.port(),
    }
  }
}

impl<S> From<SocketAddrV6> for HostAddr<S> {
  fn from(addr: SocketAddrV6) -> Self {
    Self {
      host: Host::Ip(IpAddr::V6(*addr.ip())),
      port: addr.port(),
    }
  }
}

impl<S> HostAddr<S> {
  /// Create a new host address
  #[inline]
  pub const fn new(host: Host<S>, port: u16) -> Self {
    Self { host, port }
  }

  /// Get the host name
  #[inline]
  pub const fn host(&self) -> &Host<S> {
    &self.host
  }

  /// Get the port number
  #[inline]
  pub const fn port(&self) -> u16 {
    self.port
  }

  /// Set the port number
  #[inline]
  pub const fn set_port(&mut self, port: u16) -> &mut Self {
    self.port = port;
    self
  }

  /// Set the port number
  #[inline]
  pub const fn with_port(mut self, port: u16) -> Self {
    self.port = port;
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

  /// Map the host name
  #[inline]
  pub fn map_host<F, T>(self, f: F) -> HostAddr<T>
  where
    F: FnOnce(Host<S>) -> Host<T>,
  {
    HostAddr {
      host: f(self.host),
      port: self.port,
    }
  }

  /// Returns `true` if the host is an IP address
  #[inline]
  pub const fn is_ip(&self) -> bool {
    self.host.is_ip()
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
  /// assert_eq!("example.com", &**host.as_ref().host().unwrap_domain().into_inner());
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
  /// assert_eq!("example.com", host.as_deref().host().unwrap_domain().into_inner());
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
}

impl<S> FromStr for HostAddr<S>
where
  Domain<S>: FromStr,
{
  type Err = ParseHostAddrError;

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    if let Ok(addr) = SocketAddr::from_str(s) {
      return Ok(Self::from(addr));
    }

    let mut parts = s.splitn(2, ':');
    let host = parts
      .next()
      .ok_or(ParseHostAddrError::Host(ParseHostError(())))?
      .parse()?;
    let port = parts
      .next()
      .ok_or(ParseHostAddrError::PortNotFound)?
      .parse()?;

    Ok(Self { host, port })
  }
}

impl<'a, S> TryFrom<&'a str> for HostAddr<S>
where
  Domain<S>: TryFrom<&'a str>,
{
  type Error = ParseHostAddrError;

  fn try_from(s: &'a str) -> Result<Self, Self::Error> {
    if let Ok(addr) = SocketAddr::from_str(s) {
      return Ok(Self::from(addr));
    }

    let mut parts = s.splitn(2, ':');
    let host = parts
      .next()
      .ok_or(ParseHostAddrError::Host(ParseHostError(())))?
      .try_into()?;
    let port = parts
      .next()
      .ok_or(ParseHostAddrError::PortNotFound)?
      .parse()?;

    Ok(Self { host, port })
  }
}

#[cfg(any(feature = "arbitrary", test))]
mod arbitrary_impl;
#[cfg(any(feature = "quickcheck", test))]
mod quickcheck_impl;

#[cfg(test)]
mod test;
