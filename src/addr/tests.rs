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

#[cfg(any(feature = "std", feature = "alloc"))]
#[test]
fn hostaddr_conversions_and_accessors_cover_public_contract() {
  use std::{boxed::Box, string::String};

  let domain = Domain::<String>::try_from("example.com").unwrap();
  let from_domain = HostAddr::<String>::from(domain);
  assert_eq!(
    from_domain.as_ref().unwrap_domain().0.as_str(),
    "example.com"
  );
  assert_eq!(from_domain.port(), None);

  let domain = Domain::<String>::try_from("example.com").unwrap();
  let domain_port = HostAddr::<String>::from((domain, 443));
  assert_eq!(domain_port.port(), Some(443));

  let domain = Domain::<String>::try_from("example.org").unwrap();
  let port_domain = HostAddr::<String>::from((8443, domain));
  assert_eq!(port_domain.port(), Some(8443));

  let ip: IpAddr = "127.0.0.1".parse().unwrap();
  assert_eq!(HostAddr::<String>::from(ip).unwrap_ip().0, ip);
  assert_eq!(HostAddr::<String>::from((ip, 80)).port(), Some(80));
  assert_eq!(HostAddr::<String>::from((81, ip)).port(), Some(81));

  let v4 = Ipv4Addr::new(127, 0, 0, 1);
  assert_eq!(HostAddr::<String>::from(v4).unwrap_ip().0, IpAddr::V4(v4));
  assert_eq!(
    HostAddr::<String>::from((v4, 82)).to_socket_addr(),
    Some(SocketAddr::new(IpAddr::V4(v4), 82))
  );

  let v6 = Ipv6Addr::LOCALHOST;
  assert_eq!(HostAddr::<String>::from(v6).unwrap_ip().0, IpAddr::V6(v6));
  assert_eq!(
    HostAddr::<String>::from((v6, 83)).to_socket_addr(),
    Some(SocketAddr::new(IpAddr::V6(v6), 83))
  );

  let sock: SocketAddr = "127.0.0.1:8080".parse().unwrap();
  assert_eq!(HostAddr::<String>::from(sock).to_socket_addr(), Some(sock));
  let sock_v4: SocketAddrV4 = "127.0.0.1:8081".parse().unwrap();
  assert_eq!(
    HostAddr::<String>::from(sock_v4).to_socket_addr(),
    Some(SocketAddr::V4(sock_v4))
  );
  let sock_v6: SocketAddrV6 = "[::1]:8082".parse().unwrap();
  assert_eq!(
    HostAddr::<String>::from(sock_v6).to_socket_addr(),
    Some(SocketAddr::V6(sock_v6))
  );

  let mut mutable = HostAddr::new(Host::from(
    Domain::<String>::try_from("example.net").unwrap(),
  ));
  assert!(mutable.is_domain());
  assert!(!mutable.has_port());
  assert!(mutable.ip().is_none());
  assert_eq!(
    mutable.host().domain().map(String::as_str),
    Some("example.net")
  );
  mutable.set_port(9000);
  assert!(mutable.has_port());
  mutable.maybe_port(None);
  assert!(!mutable.has_port());
  mutable.maybe_port(Some(9001));
  assert_eq!(mutable.port(), Some(9001));
  assert_eq!(
    mutable.clone().maybe_with_port(Some(9003)).port(),
    Some(9003)
  );
  mutable.clear_port();
  assert_eq!(mutable.port(), None);
  mutable.set_host(Host::from_ip(IpAddr::V4(v4)));
  assert!(mutable.is_ip());
  assert!(mutable.is_ipv4());
  assert!(!mutable.is_ipv6());
  assert_eq!(
    mutable.with_port(9002).to_socket_addr(),
    Some(SocketAddr::new(IpAddr::V4(v4), 9002))
  );

  let defaulted = HostAddr::<String>::from_ip_addr(IpAddr::V6(v6)).with_default_port(443);
  assert_eq!(defaulted.port(), Some(443));
  assert!(defaulted.is_ipv6());
  let already_set = defaulted.with_default_port(8443);
  assert_eq!(already_set.port(), Some(443));
  assert_eq!(already_set.unwrap_ip(), (IpAddr::V6(v6), Some(443)));

  let with_host = HostAddr::<String>::from_ip_addr(IpAddr::V4(v4)).with_host(Host::from(
    Domain::<String>::try_from("example.io").unwrap(),
  ));
  assert!(with_host.is_domain());
  assert_eq!(with_host.to_socket_addr(), None);
  assert_eq!(with_host.unwrap_domain().0.as_str(), "example.io");

  assert!(HostAddr::try_from_ascii_str("127.0.0.1").unwrap().is_ipv4());
  assert_eq!(
    HostAddr::try_from_ascii_str("example.com:25")
      .unwrap()
      .port(),
    Some(25)
  );
  assert_eq!(
    HostAddr::try_from_ascii_bytes(b"example.com:26")
      .unwrap()
      .port(),
    Some(26)
  );
  assert!(HostAddr::try_from_ascii_bytes(b"@a:26").is_err());
  assert!(HostAddr::try_from_ascii_bytes(b"127.0.0.1")
    .unwrap()
    .is_ipv4());

  let ascii = HostAddr::try_from_ascii_str("example.com").unwrap();
  assert_eq!(ascii.as_bytes().unwrap_domain().0, b"example.com");
  let ascii = HostAddr::try_from_ascii_bytes(b"example.com").unwrap();
  assert_eq!(ascii.as_str().unwrap_domain().0, "example.com");

  let boxed: HostAddr<Box<str>> =
    HostAddr::from(Domain::<Box<str>>::try_from("example.com").unwrap());
  assert_eq!(boxed.as_deref().unwrap_domain().0, "example.com");
  assert_eq!(
    boxed.as_ref().cloned().unwrap_domain().0.as_ref(),
    "example.com"
  );

  let buffer_addr: HostAddr<crate::Buffer> =
    HostAddr::from(Domain::<crate::Buffer>::try_from("example.com").unwrap());
  assert_eq!(
    buffer_addr.as_ref().copied().unwrap_domain().0.as_str(),
    "example.com"
  );

  let owned_domain_addr: HostAddr<Domain<String>> =
    HostAddr::<String>::from(Domain::<String>::try_from("example.com").unwrap())
      .with_port(443)
      .into();
  assert_eq!(
    owned_domain_addr
      .as_ref()
      .unwrap_domain()
      .0
      .as_inner()
      .as_str(),
    "example.com"
  );
  assert_eq!(owned_domain_addr.port(), Some(443));

  let owned_ip_addr: HostAddr<Domain<String>> = HostAddr::<String>::from_ip_addr(IpAddr::V4(v4))
    .with_port(443)
    .into();
  assert_eq!(owned_ip_addr.unwrap_ip(), (IpAddr::V4(v4), Some(443)));

  let borrowed_domain_addr: HostAddr<&Domain<String>> = (&from_domain).into();
  assert_eq!(
    borrowed_domain_addr.unwrap_domain().0.as_inner().as_str(),
    "example.com"
  );
  let ip_for_borrow = HostAddr::<String>::from_ip_addr(IpAddr::V4(v4));
  let borrowed_ip_addr: HostAddr<&Domain<String>> = (&ip_for_borrow).into();
  assert_eq!(borrowed_ip_addr.unwrap_ip().0, IpAddr::V4(v4));

  let (host, port) = HostAddr::<String>::from((IpAddr::V4(v4), 55)).into_components();
  assert_eq!(host.unwrap_ip(), IpAddr::V4(v4));
  assert_eq!(port, Some(55));

  assert!(HostAddr::try_from_ascii_str("localhost")
    .unwrap()
    .is_localhost());
  assert!(HostAddr::try_from_ascii_str("localhost.")
    .unwrap()
    .is_localhost());
  assert!(HostAddr::<String>::from_ip_addr(IpAddr::V4(v4)).is_localhost());
  assert!(HostAddr::<String>::from_ip_addr(IpAddr::V6(v6)).is_localhost());
  assert!(!HostAddr::try_from_ascii_str("example.com")
    .unwrap()
    .is_localhost());
}
