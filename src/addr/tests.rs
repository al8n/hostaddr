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
fn ipv6_parser_accepts_bare_and_bracketed_forms() {
  use std::{string::String, string::ToString};

  let forms = [
    ("2001:db8::1", None),
    ("2001:0db8:0000:0000:0000:0000:0000:0001", None),
    ("[2001:db8::1]", None),
    ("[2001:db8::1]:443", Some(443)),
  ];

  for (input, port) in forms {
    let parsed: HostAddr<String> = input.parse().unwrap();
    assert_eq!(
      parsed.as_ref().host().unwrap_ip(),
      "2001:db8::1".parse::<IpAddr>().unwrap()
    );
    assert_eq!(parsed.port(), port);

    let displayed = parsed.to_string();
    let reparsed: HostAddr<String> = displayed.parse().unwrap();
    assert_eq!(reparsed, parsed);
  }

  for input in ["2001:db8::1", "[2001:db8::1]", "[2001:db8::1]:443"] {
    let parsed = HostAddr::try_from_ascii_str(input).unwrap();
    assert!(parsed.is_ipv6());
  }

  for input in [b"2001:db8::1".as_slice(), b"[2001:db8::1]:443"] {
    let parsed = HostAddr::try_from_ascii_bytes(input).unwrap();
    assert!(parsed.is_ipv6());
  }
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
fn hostaddr_domain_equality_ordering_and_hash_follow_storage_representation() {
  use std::string::String;

  let lower: HostAddr<String> = "example.com:80".parse().unwrap();
  let upper: HostAddr<String> = "EXAMPLE.COM:80".parse().unwrap();
  assert_ne!(lower, upper);
  assert_ne!(lower.cmp(&upper), core::cmp::Ordering::Equal);

  #[cfg(feature = "std")]
  {
    use std::collections::HashSet;

    let mut set = HashSet::new();
    set.insert(lower);
    set.insert(upper.clone());
    assert_eq!(set.len(), 2);
  }

  let different_port: HostAddr<String> = "EXAMPLE.COM:81".parse().unwrap();
  assert_ne!(upper, different_port);
  assert!(upper < different_port);

  let fqdn: HostAddr<String> = "example.com.:80".parse().unwrap();
  assert_ne!(upper, fqdn);

  let ip_lower: HostAddr<String> = "127.0.0.1:80".parse().unwrap();
  let ip_upper: HostAddr<String> = "127.0.0.1:80".parse().unwrap();
  assert_eq!(ip_lower, ip_upper);
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

  let scoped = SocketAddrV6::new(v6, 8083, 0x1234, 7);
  let host = HostAddr::<String>::from(scoped);
  assert_eq!(host.port(), Some(8083));
  assert_eq!(
    host.to_socket_addr(),
    Some(SocketAddr::V6(SocketAddrV6::new(v6, 8083, 0, 0)))
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

#[cfg(all(feature = "serde", any(feature = "std", feature = "alloc")))]
#[test]
fn hostaddr_deserialize_validates_and_normalizes_domain_hosts() {
  use std::{string::String, vec::Vec};

  #[derive(serde::Serialize)]
  #[serde(rename_all = "snake_case")]
  #[allow(dead_code)]
  enum RawHost<T> {
    Ip(IpAddr),
    Domain(T),
  }

  #[derive(serde::Serialize)]
  struct RawHostAddr<T> {
    host: RawHost<T>,
    port: Option<u16>,
  }

  for invalid in ["", "-example.com", "example-.com", "example.123"] {
    let invalid = RawHostAddr {
      host: RawHost::Domain(String::from(invalid)),
      port: Some(443),
    };

    let json = serde_json::to_string(&invalid).unwrap();
    assert!(serde_json::from_str::<HostAddr<String>>(&json).is_err());
    let bincode = bincode::serialize(&invalid).unwrap();
    assert!(bincode::deserialize::<HostAddr<String>>(&bincode).is_err());
    let msgpack = rmp_serde::to_vec(&invalid).unwrap();
    assert!(rmp_serde::from_slice::<HostAddr<String>>(&msgpack).is_err());
  }

  let invalid_utf8 = RawHostAddr {
    host: RawHost::Domain(Vec::from([0xff])),
    port: None,
  };
  let json = serde_json::to_string(&invalid_utf8).unwrap();
  assert!(serde_json::from_str::<HostAddr<Vec<u8>>>(&json).is_err());
  let bincode = bincode::serialize(&invalid_utf8).unwrap();
  assert!(bincode::deserialize::<HostAddr<Vec<u8>>>(&bincode).is_err());
  let msgpack = rmp_serde::to_vec(&invalid_utf8).unwrap();
  assert!(rmp_serde::from_slice::<HostAddr<Vec<u8>>>(&msgpack).is_err());

  for (encoded, expected) in [
    ("example.com", "example.com"),
    ("测试.中国", "xn--0zwm56d.xn--fiqs8s"),
  ] {
    let raw = RawHostAddr {
      host: RawHost::Domain(String::from(encoded)),
      port: Some(8443),
    };

    let json = serde_json::to_string(&raw).unwrap();
    let addr: HostAddr<String> = serde_json::from_str(&json).unwrap();
    assert_eq!(addr.unwrap_domain(), (String::from(expected), Some(8443)));

    let bincode = bincode::serialize(&raw).unwrap();
    let addr: HostAddr<String> = bincode::deserialize(&bincode).unwrap();
    assert_eq!(addr.unwrap_domain(), (String::from(expected), Some(8443)));

    let msgpack = rmp_serde::to_vec(&raw).unwrap();
    let addr: HostAddr<String> = rmp_serde::from_slice(&msgpack).unwrap();
    assert_eq!(addr.unwrap_domain(), (String::from(expected), Some(8443)));
  }
}

#[cfg(all(feature = "serde", any(feature = "std", feature = "alloc")))]
#[test]
fn cow_hostaddr_serde_validates_owned_and_borrowed_storage() {
  use std::{borrow::Cow, fmt::Debug, string::String, vec::Vec};

  #[derive(serde::Serialize)]
  #[serde(rename_all = "snake_case")]
  #[allow(dead_code)]
  enum RawHost<T> {
    Ip(IpAddr),
    Domain(T),
  }

  #[derive(serde::Serialize)]
  struct RawHostAddr<T> {
    host: RawHost<T>,
    port: Option<u16>,
  }

  fn assert_roundtrips<T>(value: &T)
  where
    T: serde::Serialize + serde::de::DeserializeOwned + PartialEq + Debug,
  {
    let json = serde_json::to_string(value).unwrap();
    assert_eq!(serde_json::from_str::<T>(&json).unwrap(), *value);

    let bincode = bincode::serialize(value).unwrap();
    assert_eq!(bincode::deserialize::<T>(&bincode).unwrap(), *value);

    let msgpack = rmp_serde::to_vec(value).unwrap();
    assert_eq!(rmp_serde::from_slice::<T>(&msgpack).unwrap(), *value);
  }

  fn assert_rejected<T, W>(wire: &W)
  where
    T: serde::de::DeserializeOwned,
    W: serde::Serialize,
  {
    let json = serde_json::to_string(wire).unwrap();
    assert!(serde_json::from_str::<T>(&json).is_err());

    let bincode = bincode::serialize(wire).unwrap();
    assert!(bincode::deserialize::<T>(&bincode).is_err());

    let msgpack = rmp_serde::to_vec(wire).unwrap();
    assert!(rmp_serde::from_slice::<T>(&msgpack).is_err());
  }

  fn assert_str_normalizes(value: &RawHostAddr<Cow<'static, str>>, expected: &str) {
    let json = serde_json::to_string(value).unwrap();
    let decoded: HostAddr<Cow<'static, str>> = serde_json::from_str(&json).unwrap();
    assert_eq!(decoded.unwrap_domain().0.as_ref(), expected);

    let bincode = bincode::serialize(value).unwrap();
    let decoded: HostAddr<Cow<'static, str>> = bincode::deserialize(&bincode).unwrap();
    assert_eq!(decoded.unwrap_domain().0.as_ref(), expected);

    let msgpack = rmp_serde::to_vec(value).unwrap();
    let decoded: HostAddr<Cow<'static, str>> = rmp_serde::from_slice(&msgpack).unwrap();
    assert_eq!(decoded.unwrap_domain().0.as_ref(), expected);
  }

  fn assert_bytes_normalizes(value: &RawHostAddr<Cow<'static, [u8]>>, expected: &[u8]) {
    let json = serde_json::to_string(value).unwrap();
    let decoded: HostAddr<Cow<'static, [u8]>> = serde_json::from_str(&json).unwrap();
    assert_eq!(decoded.unwrap_domain().0.as_ref(), expected);

    let bincode = bincode::serialize(value).unwrap();
    let decoded: HostAddr<Cow<'static, [u8]>> = bincode::deserialize(&bincode).unwrap();
    assert_eq!(decoded.unwrap_domain().0.as_ref(), expected);

    let msgpack = rmp_serde::to_vec(value).unwrap();
    let decoded: HostAddr<Cow<'static, [u8]>> = rmp_serde::from_slice(&msgpack).unwrap();
    assert_eq!(decoded.unwrap_domain().0.as_ref(), expected);
  }

  let borrowed: HostAddr<Cow<'static, str>> =
    HostAddr::from(Domain::try_from(Cow::Borrowed("example.com")).unwrap()).with_port(443);
  assert_roundtrips(&borrowed);
  let owned: HostAddr<Cow<'static, str>> =
    HostAddr::from(Domain::try_from(Cow::Owned(String::from("example.org"))).unwrap());
  assert_roundtrips(&owned);

  let borrowed: HostAddr<Cow<'static, [u8]>> =
    HostAddr::from(Domain::try_from(Cow::Borrowed(&b"example.com"[..])).unwrap()).with_port(443);
  assert_roundtrips(&borrowed);
  let owned: HostAddr<Cow<'static, [u8]>> =
    HostAddr::from(Domain::try_from(Cow::Owned(Vec::from(&b"example.org"[..]))).unwrap());
  assert_roundtrips(&owned);

  for (input, expected) in [
    ("测试.中国", "xn--0zwm56d.xn--fiqs8s"),
    ("example%2Ecom", "example.com"),
  ] {
    assert_str_normalizes(
      &RawHostAddr {
        host: RawHost::Domain(Cow::Borrowed(input)),
        port: Some(443),
      },
      expected,
    );
    assert_bytes_normalizes(
      &RawHostAddr {
        host: RawHost::Domain(Cow::Borrowed(input.as_bytes())),
        port: Some(443),
      },
      expected.as_bytes(),
    );
  }

  let invalid = RawHostAddr {
    host: RawHost::Domain(Cow::Borrowed("")),
    port: None,
  };
  assert_rejected::<HostAddr<Cow<'static, str>>, _>(&invalid);
  let invalid: RawHostAddr<Cow<'static, str>> = RawHostAddr {
    host: RawHost::Domain(Cow::Owned(String::from("example.123"))),
    port: Some(443),
  };
  assert_rejected::<HostAddr<Cow<'static, str>>, _>(&invalid);
  let invalid = RawHostAddr {
    host: RawHost::Domain(Cow::Borrowed(&[0xff][..])),
    port: None,
  };
  assert_rejected::<HostAddr<Cow<'static, [u8]>>, _>(&invalid);
  let invalid: RawHostAddr<Cow<'static, [u8]>> = RawHostAddr {
    host: RawHost::Domain(Cow::Owned(Vec::from(&b"-example.com"[..]))),
    port: Some(443),
  };
  assert_rejected::<HostAddr<Cow<'static, [u8]>>, _>(&invalid);
}
