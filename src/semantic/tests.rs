use super::*;

fn parse_ip(s: &str) -> IpAddr {
  s.parse().unwrap()
}

fn sock(ip: IpAddr) -> SocketAddr {
  SocketAddr::new(ip, 443)
}

macro_rules! assert_addr_class {
    ($ip_ty:ty, $addr_ty:ty, [$($valid:literal),+ $(,)?], [$($invalid:literal),+ $(,)?]) => {{
      $(
        let parsed_ip = parse_ip($valid);
        let ip_addr = <$ip_ty>::try_from(parsed_ip).unwrap();
        assert_eq!(ip_addr.as_ip_addr(), parsed_ip, $valid);
        assert_eq!(ip_addr.into_ip_addr(), parsed_ip, $valid);

        let socket = sock(parsed_ip);
        let addr = <$addr_ty>::try_from(socket).unwrap();
        assert_eq!(addr.as_socket_addr(), socket, $valid);
        assert_eq!(addr.ip(), parsed_ip, $valid);
        assert_eq!(addr.ip_addr().as_ip_addr(), parsed_ip, $valid);
        assert_eq!(addr.port(), 443, $valid);
      )+

      $(
        let parsed_ip = parse_ip($invalid);
        assert!(<$ip_ty>::try_from(parsed_ip).is_err(), $invalid);
        assert!(<$addr_ty>::try_from(sock(parsed_ip)).is_err(), $invalid);
      )+
    }};
  }

#[test]
fn common_semantic_classes_validate_ip_and_socket_forms() {
  assert_addr_class!(
    LoopbackIpAddr,
    LoopbackAddr,
    ["127.1.2.3", "::1"],
    ["192.0.2.1", "::2"]
  );
  assert_addr_class!(
    PrivateIpAddr,
    PrivateAddr,
    [
      "10.0.0.1",
      "172.16.0.1",
      "172.31.255.255",
      "192.168.1.1",
      "fc00::1",
      "fdff::1"
    ],
    ["100.64.0.1", "172.32.0.1", "2001:db8::1"]
  );
  assert_addr_class!(
    LinkLocalIpAddr,
    LinkLocalAddr,
    ["169.254.1.1", "fe80::1"],
    ["169.255.1.1", "fc00::1"]
  );
  assert_addr_class!(
    DocumentationIpAddr,
    DocumentationAddr,
    [
      "192.0.2.1",
      "198.51.100.1",
      "203.0.113.1",
      "2001:db8::1",
      "3fff::",
      "3fff:0fff:ffff:ffff:ffff:ffff:ffff:ffff"
    ],
    ["198.18.0.1", "2001:db9::1", "3fff:1000::"]
  );
  assert_addr_class!(
    BenchmarkIpAddr,
    BenchmarkAddr,
    ["198.18.0.1", "198.19.255.255", "2001:2::1"],
    ["198.20.0.1", "2001:200::1", "2001:3::1"]
  );
  assert_addr_class!(
    SharedIpAddr,
    SharedAddr,
    ["100.64.0.1", "100.127.255.255"],
    ["100.128.0.1", "10.0.0.1", "::1"]
  );
  assert_addr_class!(
    MulticastIpAddr,
    MulticastAddr,
    ["224.0.0.1", "239.255.255.255", "ff02::1"],
    ["240.0.0.1", "fe80::1"]
  );
  assert_addr_class!(
    UnspecifiedIpAddr,
    UnspecifiedAddr,
    ["0.0.0.0", "::"],
    ["0.0.0.1", "::1"]
  );
  assert_addr_class!(
    BroadcastIpAddr,
    BroadcastAddr,
    ["255.255.255.255"],
    ["255.255.255.254", "::"]
  );
}

#[cfg(any(feature = "std", feature = "alloc"))]
#[test]
fn semantic_wrappers_cover_conversion_traits_and_display() {
  use crate::std::string::ToString as _;

  let ip_v4 = Ipv4Addr::new(127, 0, 0, 1);
  let ip_v6 = Ipv6Addr::LOCALHOST;

  let loopback_v4 = LoopbackIpAddr::try_from(ip_v4).unwrap();
  assert_eq!(loopback_v4.to_string(), "127.0.0.1");
  assert_eq!(IpAddr::from(loopback_v4), IpAddr::V4(ip_v4));

  let loopback_v6 = LoopbackIpAddr::try_from(ip_v6).unwrap();
  assert_eq!(loopback_v6.into_ip_addr(), IpAddr::V6(ip_v6));
  assert_eq!(
    LoopbackIpAddr::new(IpAddr::V4(Ipv4Addr::new(192, 0, 2, 1)))
      .unwrap_err()
      .as_str(),
    "not a loopback IP address"
  );

  let socket_v4 = SocketAddrV4::new(ip_v4, 8080);
  let loopback_addr_v4 = LoopbackAddr::try_from(socket_v4).unwrap();
  assert_eq!(loopback_addr_v4.to_string(), "127.0.0.1:8080");
  assert_eq!(
    SocketAddr::from(loopback_addr_v4),
    SocketAddr::V4(socket_v4)
  );

  let socket_v6 = SocketAddrV6::new(ip_v6, 443, 7, 42);
  let loopback_addr_v6 = LoopbackAddr::try_from(socket_v6).unwrap();
  assert_eq!(
    loopback_addr_v6.into_socket_addr(),
    SocketAddr::V6(socket_v6)
  );
  assert_eq!(
    LoopbackAddr::new(SocketAddr::new(IpAddr::V4(Ipv4Addr::new(192, 0, 2, 1)), 80))
      .unwrap_err()
      .as_str(),
    "not a loopback socket address"
  );
}

#[cfg(feature = "serde")]
#[test]
fn serde_preserves_semantic_invariants() {
  let loopback = LoopbackAddr::try_from("127.0.0.1:8080".parse::<SocketAddr>().unwrap()).unwrap();
  let serialized = serde_json::to_string(&loopback).unwrap();
  let deserialized: LoopbackAddr = serde_json::from_str(&serialized).unwrap();
  assert_eq!(deserialized, loopback);
  assert!(serde_json::from_str::<LoopbackAddr>("\"192.0.2.1:8080\"").is_err());

  let private = PrivateIpAddr::try_from(parse_ip("fd00::1")).unwrap();
  let serialized = serde_json::to_string(&private).unwrap();
  let deserialized: PrivateIpAddr = serde_json::from_str(&serialized).unwrap();
  assert_eq!(deserialized, private);
  assert!(serde_json::from_str::<PrivateIpAddr>("\"2001:db8::1\"").is_err());
}

#[cfg(feature = "serde")]
#[test]
fn serde_preserves_ipv6_socket_metadata() {
  let socket = SocketAddrV6::new("fe80::1".parse().unwrap(), 443, 7, 42);
  let addr = LinkLocalAddr::try_from(SocketAddr::V6(socket)).unwrap();

  let serialized = serde_json::to_string(&addr).unwrap();
  let deserialized: LinkLocalAddr = serde_json::from_str(&serialized).unwrap();
  assert_eq!(deserialized.as_socket_addr(), addr.as_socket_addr());

  let serialized = rmp_serde::to_vec(&addr).unwrap();
  let deserialized: LinkLocalAddr = rmp_serde::from_slice(&serialized).unwrap();
  assert_eq!(deserialized.as_socket_addr(), addr.as_socket_addr());
}
