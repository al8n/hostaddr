use super::*;

#[test]
fn test_hostaddr_parsing() {
  #[cfg(any(feature = "std", feature = "alloc"))]
  {
    use std::string::String;

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

  let host: HostAddr<&str> = HostAddr::try_from_ascii_str("[::1]").unwrap();
  assert_eq!(
    IpAddr::V6(Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 1)),
    host.as_ref().host().unwrap_ip()
  );

  let host: HostAddr<&[u8]> = HostAddr::try_from_ascii_bytes(b"[::1]").unwrap();
  assert_eq!(
    IpAddr::V6(Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 1)),
    host.as_ref().host().unwrap_ip()
  );

  let host: HostAddr<&[u8]> = HostAddr::try_from_ascii_bytes(b"::1").unwrap();
  assert_eq!(
    IpAddr::V6(Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 1)),
    host.as_ref().host().unwrap_ip()
  );

  let host: HostAddr<&str> = HostAddr::try_from_ascii_str("::1").unwrap();
  assert_eq!(
    IpAddr::V6(Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 1)),
    host.as_ref().host().unwrap_ip()
  );
}

#[cfg(any(feature = "std", feature = "alloc"))]
#[test]
fn test_hostaddr_try_into() {
  use std::string::String;

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

#[test]
fn negative_try_parse_v6() {
  let _ = try_parse_v6::<&str>("[a]").unwrap_err();
  let _ = try_parse_v6::<&str>("[a]:8080").unwrap_err();
  let _ = try_parse_v6::<&str>("[a:8080").unwrap_err();
}

#[test]
fn negative_try_from_ascii_bytes() {
  let err = HostAddr::try_from_ascii_bytes(b"example.com:aaa").unwrap_err();
  assert!(matches!(err, ParseAsciiHostAddrError::Port(_)));
}

#[test]
fn negative_try_from_ascii_str() {
  let err = HostAddr::try_from_ascii_str("example.com:aaa").unwrap_err();
  assert!(matches!(err, ParseAsciiHostAddrError::Port(_)));
}

/// Regression test: IPv6 with port must display as `[::1]:port`, not `::1:port`.
/// The old output was ambiguous and could not be parsed back.
#[test]
#[cfg(feature = "std")]
fn ipv6_display_roundtrip() {
  let addr = HostAddr::<&str>::from_sock_addr("[::1]:8080".parse().unwrap());
  assert_eq!(addr.to_string(), "[::1]:8080");

  // Without port, no brackets
  let addr = HostAddr::<&str>::from_ip_addr("::1".parse().unwrap());
  assert_eq!(addr.to_string(), "::1");

  // IPv4 unchanged
  let addr = HostAddr::<&str>::from_sock_addr("127.0.0.1:3000".parse().unwrap());
  assert_eq!(addr.to_string(), "127.0.0.1:3000");

  // Roundtrip: display then parse
  #[cfg(any(feature = "std", feature = "alloc"))]
  {
    use std::string::String;
    let addr = HostAddr::<String>::from_sock_addr("[::1]:443".parse().unwrap());
    let displayed = addr.to_string();
    let reparsed: HostAddr<String> = displayed.parse().unwrap();
    assert_eq!(reparsed.port(), Some(443));
    assert!(reparsed.is_ipv6());
  }
}
