use core::net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr, SocketAddrV4, SocketAddrV6};

use iprfc::{
  is_benchmark_ip_addr as is_benchmark_ip, is_broadcast_ip_addr as is_broadcast_ip,
  is_documentation_ip_addr as is_documentation_ip, is_link_local_ip_addr as is_link_local_ip,
  is_loopback_ip_addr as is_loopback_ip, is_multicast_ip_addr as is_multicast_ip,
  is_private_ip_addr as is_private_ip, is_shared_ip_addr as is_shared_ip,
  is_unspecified_ip_addr as is_unspecified_ip,
};

#[cfg(test)]
mod tests;

#[cfg(feature = "serde")]
#[derive(serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "snake_case")]
enum HumanSocketAddr {
  V4 {
    ip: Ipv4Addr,
    port: u16,
  },
  V6 {
    ip: Ipv6Addr,
    port: u16,
    flowinfo: u32,
    scope_id: u32,
  },
}

#[cfg(feature = "serde")]
impl HumanSocketAddr {
  #[inline]
  const fn from_socket_addr(addr: SocketAddr) -> Self {
    match addr {
      SocketAddr::V4(addr) => Self::V4 {
        ip: *addr.ip(),
        port: addr.port(),
      },
      SocketAddr::V6(addr) => Self::V6 {
        ip: *addr.ip(),
        port: addr.port(),
        flowinfo: addr.flowinfo(),
        scope_id: addr.scope_id(),
      },
    }
  }

  #[inline]
  const fn into_socket_addr(self) -> SocketAddr {
    match self {
      Self::V4 { ip, port } => SocketAddr::V4(SocketAddrV4::new(ip, port)),
      Self::V6 {
        ip,
        port,
        flowinfo,
        scope_id,
      } => SocketAddr::V6(SocketAddrV6::new(ip, port, flowinfo, scope_id)),
    }
  }
}

#[cfg(feature = "serde")]
#[derive(serde::Serialize, serde::Deserialize)]
enum BinarySocketAddr {
  V4(Ipv4Addr, u16),
  V6(Ipv6Addr, u16),
  V6Extended(Ipv6Addr, u16, u32, u32),
}

#[cfg(feature = "serde")]
impl BinarySocketAddr {
  #[inline]
  const fn from_socket_addr(addr: SocketAddr) -> Self {
    match addr {
      SocketAddr::V4(addr) => Self::V4(*addr.ip(), addr.port()),
      SocketAddr::V6(addr) if addr.flowinfo() == 0 && addr.scope_id() == 0 => {
        Self::V6(*addr.ip(), addr.port())
      }
      SocketAddr::V6(addr) => {
        Self::V6Extended(*addr.ip(), addr.port(), addr.flowinfo(), addr.scope_id())
      }
    }
  }

  #[inline]
  const fn into_socket_addr(self) -> SocketAddr {
    match self {
      Self::V4(ip, port) => SocketAddr::V4(SocketAddrV4::new(ip, port)),
      Self::V6(ip, port) => SocketAddr::V6(SocketAddrV6::new(ip, port, 0, 0)),
      Self::V6Extended(ip, port, flowinfo, scope_id) => {
        SocketAddr::V6(SocketAddrV6::new(ip, port, flowinfo, scope_id))
      }
    }
  }
}

#[cfg(feature = "serde")]
struct HumanSocketAddrVisitor;

#[cfg(feature = "serde")]
impl<'de> serde::de::Visitor<'de> for HumanSocketAddrVisitor {
  type Value = SocketAddr;

  #[inline]
  fn expecting(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    formatter.write_str("a v4/v6 socket-address object or a legacy socket-address string")
  }

  #[inline]
  fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
  where
    E: serde::de::Error,
  {
    value.parse().map_err(E::custom)
  }

  #[inline]
  fn visit_map<M>(self, map: M) -> Result<Self::Value, M::Error>
  where
    M: serde::de::MapAccess<'de>,
  {
    use serde::Deserialize as _;

    HumanSocketAddr::deserialize(serde::de::value::MapAccessDeserializer::new(map))
      .map(HumanSocketAddr::into_socket_addr)
  }
}

#[cfg(feature = "serde")]
#[inline]
fn serialize_socket_addr<S>(addr: SocketAddr, serializer: S) -> Result<S::Ok, S::Error>
where
  S: serde::Serializer,
{
  use serde::Serialize as _;

  if serializer.is_human_readable() {
    HumanSocketAddr::from_socket_addr(addr).serialize(serializer)
  } else {
    BinarySocketAddr::from_socket_addr(addr).serialize(serializer)
  }
}

#[cfg(feature = "serde")]
#[inline]
fn deserialize_socket_addr<'de, D>(deserializer: D) -> Result<SocketAddr, D::Error>
where
  D: serde::Deserializer<'de>,
{
  use serde::Deserialize as _;

  if deserializer.is_human_readable() {
    deserializer.deserialize_any(HumanSocketAddrVisitor)
  } else {
    BinarySocketAddr::deserialize(deserializer).map(BinarySocketAddr::into_socket_addr)
  }
}

macro_rules! semantic_addr_class {
  (
    ip: $ip_name:ident, $ip_error:ident, $ip_doc:literal, $ip_error_doc:literal, $ip_error_msg:literal;
    addr: $addr_name:ident, $addr_error:ident, $addr_doc:literal, $addr_error_doc:literal, $addr_error_msg:literal;
    predicate: $predicate:ident;
  ) => {
    #[doc = $ip_doc]
    #[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
    #[repr(transparent)]
    #[cfg_attr(feature = "serde", derive(serde::Serialize))]
    #[cfg_attr(feature = "serde", serde(transparent))]
    pub struct $ip_name(IpAddr);

    #[cfg(feature = "serde")]
    impl<'de> serde::Deserialize<'de> for $ip_name {
      #[inline]
      fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
      where
        D: serde::Deserializer<'de>,
      {
        let ip = IpAddr::deserialize(deserializer)?;
        Self::new(ip).map_err(serde::de::Error::custom)
      }
    }

    impl $ip_name {
      /// Creates the address after validating the IP address.
      #[inline]
      pub const fn new(ip: IpAddr) -> Result<Self, $ip_error> {
        if $predicate(ip) {
          Ok(Self(ip))
        } else {
          Err($ip_error(()))
        }
      }

      /// Returns the inner IP address.
      #[inline]
      pub const fn as_ip_addr(&self) -> IpAddr {
        self.0
      }

      /// Returns the inner IP address by value.
      #[inline]
      pub const fn into_ip_addr(self) -> IpAddr {
        self.0
      }
    }

    impl core::fmt::Display for $ip_name {
      #[inline]
      fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.0.fmt(f)
      }
    }

    impl TryFrom<IpAddr> for $ip_name {
      type Error = $ip_error;

      #[inline]
      fn try_from(value: IpAddr) -> Result<Self, Self::Error> {
        Self::new(value)
      }
    }

    impl TryFrom<Ipv4Addr> for $ip_name {
      type Error = $ip_error;

      #[inline]
      fn try_from(value: Ipv4Addr) -> Result<Self, Self::Error> {
        Self::new(IpAddr::V4(value))
      }
    }

    impl TryFrom<Ipv6Addr> for $ip_name {
      type Error = $ip_error;

      #[inline]
      fn try_from(value: Ipv6Addr) -> Result<Self, Self::Error> {
        Self::new(IpAddr::V6(value))
      }
    }

    impl From<$ip_name> for IpAddr {
      #[inline]
      fn from(value: $ip_name) -> Self {
        value.into_ip_addr()
      }
    }

    #[doc = $ip_error_doc]
    #[derive(Clone, Copy, Debug, Eq, PartialEq, thiserror::Error)]
    #[error("{}", self.as_str())]
    pub struct $ip_error(());

    impl $ip_error {
      /// Returns the error message.
      #[inline]
      pub const fn as_str(&self) -> &'static str {
        $ip_error_msg
      }
    }

    #[doc = $addr_doc]
    #[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
    #[repr(transparent)]
    pub struct $addr_name(SocketAddr);

    #[cfg(feature = "serde")]
    impl serde::Serialize for $addr_name {
      #[inline]
      fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
      where
        S: serde::Serializer,
      {
        serialize_socket_addr(self.0, serializer)
      }
    }

    #[cfg(feature = "serde")]
    impl<'de> serde::Deserialize<'de> for $addr_name {
      #[inline]
      fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
      where
        D: serde::Deserializer<'de>,
      {
        let addr = deserialize_socket_addr(deserializer)?;
        Self::new(addr).map_err(serde::de::Error::custom)
      }
    }

    impl $addr_name {
      /// Creates the address after validating the IP component.
      #[inline]
      pub const fn new(addr: SocketAddr) -> Result<Self, $addr_error> {
        if $predicate(addr.ip()) {
          Ok(Self(addr))
        } else {
          Err($addr_error(()))
        }
      }

      /// Returns the inner socket address.
      #[inline]
      pub const fn as_socket_addr(&self) -> SocketAddr {
        self.0
      }

      /// Returns the inner socket address by value.
      #[inline]
      pub const fn into_socket_addr(self) -> SocketAddr {
        self.0
      }

      /// Returns the validated IP address wrapper.
      #[inline]
      pub const fn ip_addr(&self) -> $ip_name {
        $ip_name(self.0.ip())
      }

      /// Returns the IP address.
      #[inline]
      pub const fn ip(&self) -> IpAddr {
        self.0.ip()
      }

      /// Returns the socket port.
      #[inline]
      pub const fn port(&self) -> u16 {
        self.0.port()
      }
    }

    impl core::fmt::Display for $addr_name {
      #[inline]
      fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.0.fmt(f)
      }
    }

    impl TryFrom<SocketAddr> for $addr_name {
      type Error = $addr_error;

      #[inline]
      fn try_from(value: SocketAddr) -> Result<Self, Self::Error> {
        Self::new(value)
      }
    }

    impl TryFrom<SocketAddrV4> for $addr_name {
      type Error = $addr_error;

      #[inline]
      fn try_from(value: SocketAddrV4) -> Result<Self, Self::Error> {
        Self::new(SocketAddr::V4(value))
      }
    }

    impl TryFrom<SocketAddrV6> for $addr_name {
      type Error = $addr_error;

      #[inline]
      fn try_from(value: SocketAddrV6) -> Result<Self, Self::Error> {
        Self::new(SocketAddr::V6(value))
      }
    }

    impl From<$addr_name> for SocketAddr {
      #[inline]
      fn from(value: $addr_name) -> Self {
        value.into_socket_addr()
      }
    }

    #[doc = $addr_error_doc]
    #[derive(Clone, Copy, Debug, Eq, PartialEq, thiserror::Error)]
    #[error("{}", self.as_str())]
    pub struct $addr_error(());

    impl $addr_error {
      /// Returns the error message.
      #[inline]
      pub const fn as_str(&self) -> &'static str {
        $addr_error_msg
      }
    }
  };
}

semantic_addr_class! {
  ip: LoopbackIpAddr,
  ParseLoopbackIpAddrError,
  "An IP address in the loopback range.",
  "The provided IP address is not a loopback address.",
  "not a loopback IP address";
  addr: LoopbackAddr,
  ParseLoopbackAddrError,
  "A socket address whose IP address is loopback.",
  "The provided socket address is not a loopback address.",
  "not a loopback socket address";
  predicate: is_loopback_ip;
}

semantic_addr_class! {
  ip: PrivateIpAddr,
  ParsePrivateIpAddrError,
  "An RFC 1918 IPv4 private-use or RFC 4193 IPv6 unique-local address.",
  "The provided IP address is not private-use or unique-local.",
  "not a private-use or unique-local IP address";
  addr: PrivateAddr,
  ParsePrivateAddrError,
  "A socket address whose IP address is private-use or unique-local.",
  "The provided socket address is not private-use or unique-local.",
  "not a private-use or unique-local socket address";
  predicate: is_private_ip;
}

semantic_addr_class! {
  ip: LinkLocalIpAddr,
  ParseLinkLocalIpAddrError,
  "An IPv4 or IPv6 link-local address.",
  "The provided IP address is not link-local.",
  "not a link-local IP address";
  addr: LinkLocalAddr,
  ParseLinkLocalAddrError,
  "A socket address whose IP address is link-local.",
  "The provided socket address is not link-local.",
  "not a link-local socket address";
  predicate: is_link_local_ip;
}

semantic_addr_class! {
  ip: DocumentationIpAddr,
  ParseDocumentationIpAddrError,
  "An IP address reserved for documentation or examples.",
  "The provided IP address is not reserved for documentation.",
  "not a documentation IP address";
  addr: DocumentationAddr,
  ParseDocumentationAddrError,
  "A socket address whose IP address is reserved for documentation or examples.",
  "The provided socket address is not reserved for documentation.",
  "not a documentation socket address";
  predicate: is_documentation_ip;
}

semantic_addr_class! {
  ip: BenchmarkIpAddr,
  ParseBenchmarkIpAddrError,
  "An IP address reserved for benchmarking.",
  "The provided IP address is not reserved for benchmarking.",
  "not a benchmarking IP address";
  addr: BenchmarkAddr,
  ParseBenchmarkAddrError,
  "A socket address whose IP address is reserved for benchmarking.",
  "The provided socket address is not reserved for benchmarking.",
  "not a benchmarking socket address";
  predicate: is_benchmark_ip;
}

semantic_addr_class! {
  ip: SharedIpAddr,
  ParseSharedIpAddrError,
  "An IPv4 shared address space address.",
  "The provided IP address is not in IPv4 shared address space.",
  "not an IPv4 shared address space IP address";
  addr: SharedAddr,
  ParseSharedAddrError,
  "A socket address whose IP address is in IPv4 shared address space.",
  "The provided socket address is not in IPv4 shared address space.",
  "not an IPv4 shared address space socket address";
  predicate: is_shared_ip;
}

semantic_addr_class! {
  ip: MulticastIpAddr,
  ParseMulticastIpAddrError,
  "An IPv4 or IPv6 multicast address.",
  "The provided IP address is not multicast.",
  "not a multicast IP address";
  addr: MulticastAddr,
  ParseMulticastAddrError,
  "A socket address whose IP address is multicast.",
  "The provided socket address is not multicast.",
  "not a multicast socket address";
  predicate: is_multicast_ip;
}

semantic_addr_class! {
  ip: UnspecifiedIpAddr,
  ParseUnspecifiedIpAddrError,
  "The exact IPv4 or IPv6 unspecified address.",
  "The provided IP address is not the exact unspecified address.",
  "not an unspecified IP address";
  addr: UnspecifiedAddr,
  ParseUnspecifiedAddrError,
  "A socket address whose IP address is the exact unspecified address.",
  "The provided socket address is not the exact unspecified address.",
  "not an unspecified socket address";
  predicate: is_unspecified_ip;
}

semantic_addr_class! {
  ip: BroadcastIpAddr,
  ParseBroadcastIpAddrError,
  "The IPv4 limited broadcast address.",
  "The provided IP address is not the IPv4 limited broadcast address.",
  "not an IPv4 limited broadcast IP address";
  addr: BroadcastAddr,
  ParseBroadcastAddrError,
  "A socket address whose IP address is the IPv4 limited broadcast address.",
  "The provided socket address is not the IPv4 limited broadcast address.",
  "not an IPv4 limited broadcast socket address";
  predicate: is_broadcast_ip;
}
