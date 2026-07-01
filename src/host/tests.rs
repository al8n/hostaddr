use super::*;
#[cfg(any(feature = "std", feature = "alloc"))]
use std::string::String;

#[cfg(any(feature = "std", feature = "alloc"))]
#[test]
fn negative_from_str() {
  let err = "@a".parse::<Host<String>>().unwrap_err();
  assert_eq!(err.as_str(), "invalid host");
}

#[cfg(any(feature = "std", feature = "alloc"))]
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

#[cfg(any(feature = "std", feature = "alloc"))]
#[test]
fn host_conversions_and_accessors_cover_public_contract() {
  use std::{boxed::Box, string::String};

  let domain = Domain::<String>::try_from("example.com").unwrap();
  let host = Host::from(domain);
  assert!(host.is_domain());
  assert_eq!(host.domain().map(String::as_str), Some("example.com"));
  assert!(host.ip().is_none());

  let ip: IpAddr = "127.0.0.1".parse().unwrap();
  let host = Host::<String>::from(ip);
  assert!(host.is_ip());
  assert!(host.is_ipv4());
  assert!(!host.is_ipv6());
  assert_eq!(host.ip().copied(), Some(ip));
  assert!(host.domain().is_none());

  let v4 = Ipv4Addr::new(127, 0, 0, 1);
  assert_eq!(Host::<String>::from(v4).unwrap_ip(), IpAddr::V4(v4));
  let v6 = Ipv6Addr::LOCALHOST;
  assert_eq!(Host::<String>::from(v6).unwrap_ip(), IpAddr::V6(v6));
  assert!(Host::<String>::from_ip(IpAddr::V6(v6)).is_ipv6());

  let ascii_domain = Host::try_from_ascii_str("example.com").unwrap();
  assert_eq!(ascii_domain.as_bytes().unwrap_domain(), b"example.com");
  let ascii_ip = Host::try_from_ascii_str("127.0.0.1").unwrap();
  assert_eq!(ascii_ip.as_bytes().unwrap_ip(), IpAddr::V4(v4));

  let bytes_domain = Host::try_from_ascii_bytes(b"example.com").unwrap();
  assert_eq!(bytes_domain.as_str().unwrap_domain(), "example.com");
  let bytes_ip = Host::try_from_ascii_bytes(b"127.0.0.1").unwrap();
  assert_eq!(bytes_ip.as_str().unwrap_ip(), IpAddr::V4(v4));
  assert!(Host::try_from_ascii_bytes("测试.中国".as_bytes()).is_err());

  let boxed: Host<Box<str>> = Host::from(Domain::<Box<str>>::try_from("example.com").unwrap());
  assert_eq!(boxed.as_deref().unwrap_domain(), "example.com");
  assert_eq!(
    boxed.as_ref().cloned().unwrap_domain().as_ref(),
    "example.com"
  );
  let boxed_ip: Host<Box<str>> = Host::from_ip(IpAddr::V4(v4));
  assert_eq!(boxed_ip.as_deref().unwrap_ip(), IpAddr::V4(v4));

  let buffer_host: Host<crate::Buffer> = Host::try_from("example.com").unwrap();
  assert_eq!(
    buffer_host.as_ref().copied().unwrap_domain().as_str(),
    "example.com"
  );

  let ip_host: Host<&str> = Host::from_ip(IpAddr::V4(v4));
  assert_eq!(ip_host.as_ref().copied().unwrap_ip(), IpAddr::V4(v4));
  assert_eq!(ip_host.as_ref().cloned().unwrap_ip(), IpAddr::V4(v4));
}

#[test]
#[should_panic(expected = "A Host<&str> should always be valid UTF-8")]
fn host_bytes_as_str_panics_for_invalid_utf8_domain_storage() {
  let invalid: Host<&[u8]> = Host::Domain(&[0xff]);
  let _ = invalid.as_str();
}
