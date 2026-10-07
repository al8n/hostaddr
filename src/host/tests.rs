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
  assert_eq!(
    host.as_domain().map(|domain| domain.as_inner().as_str()),
    Some("example.com")
  );
  assert_eq!(host.unwrap_domain_ref(), "example.com");
  assert!(host.ip().is_none());

  let mut host = host;
  *host.unwrap_domain_mut() = Domain::try_from("example.org").unwrap();
  assert_eq!(host.unwrap_domain_ref(), "example.org");

  let ip: IpAddr = "127.0.0.1".parse().unwrap();
  let host = Host::<String>::from(ip);
  assert!(host.is_ip());
  assert!(host.is_ipv4());
  assert!(!host.is_ipv6());
  assert_eq!(host.ip().copied(), Some(ip));
  assert_eq!(host.unwrap_ip_ref(), &ip);
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
fn host_domain_variant_requires_validated_storage() {
  assert!(Domain::<&[u8]>::try_from(&[0xff][..]).is_err());
  let domain = Domain::<&[u8]>::try_from(&b"example.com"[..]).unwrap();
  let host = Host::Domain(domain);
  assert_eq!(host.as_str().unwrap_domain(), "example.com");
}

#[cfg(all(feature = "serde", any(feature = "std", feature = "alloc")))]
#[test]
fn host_deserialize_validates_and_normalizes_domain_variants() {
  use std::{string::String, vec::Vec};

  #[derive(serde::Serialize)]
  #[serde(rename_all = "snake_case")]
  #[allow(dead_code)]
  enum RawHost<T> {
    Ip(IpAddr),
    Domain(T),
  }

  for invalid in ["", "-example.com", "example-.com", "example.123"] {
    let invalid = RawHost::Domain(String::from(invalid));

    let json = serde_json::to_string(&invalid).unwrap();
    assert!(serde_json::from_str::<Host<String>>(&json).is_err());
    let bincode = bincode::serialize(&invalid).unwrap();
    assert!(bincode::deserialize::<Host<String>>(&bincode).is_err());
    let msgpack = rmp_serde::to_vec(&invalid).unwrap();
    assert!(rmp_serde::from_slice::<Host<String>>(&msgpack).is_err());
  }

  let invalid_utf8 = RawHost::Domain(Vec::from([0xff]));
  let json = serde_json::to_string(&invalid_utf8).unwrap();
  assert!(serde_json::from_str::<Host<Vec<u8>>>(&json).is_err());
  let bincode = bincode::serialize(&invalid_utf8).unwrap();
  assert!(bincode::deserialize::<Host<Vec<u8>>>(&bincode).is_err());
  let msgpack = rmp_serde::to_vec(&invalid_utf8).unwrap();
  assert!(rmp_serde::from_slice::<Host<Vec<u8>>>(&msgpack).is_err());

  for (encoded, expected) in [
    ("example.com", "example.com"),
    ("测试.中国", "xn--0zwm56d.xn--fiqs8s"),
  ] {
    let raw = RawHost::Domain(String::from(encoded));

    let json = serde_json::to_string(&raw).unwrap();
    let host: Host<String> = serde_json::from_str(&json).unwrap();
    assert_eq!(host.unwrap_domain(), expected);

    let bincode = bincode::serialize(&raw).unwrap();
    let host: Host<String> = bincode::deserialize(&bincode).unwrap();
    assert_eq!(host.unwrap_domain(), expected);

    let msgpack = rmp_serde::to_vec(&raw).unwrap();
    let host: Host<String> = rmp_serde::from_slice(&msgpack).unwrap();
    assert_eq!(host.unwrap_domain(), expected);
  }
}

#[cfg(all(feature = "serde", any(feature = "std", feature = "alloc")))]
#[test]
fn cow_host_serde_validates_owned_and_borrowed_storage() {
  use std::{borrow::Cow, fmt::Debug, string::String, vec::Vec};

  #[derive(serde::Serialize)]
  #[serde(rename_all = "snake_case")]
  #[allow(dead_code)]
  enum RawHost<T> {
    Ip(IpAddr),
    Domain(T),
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

  fn assert_str_normalizes(value: &RawHost<Cow<'static, str>>, expected: &str) {
    let json = serde_json::to_string(value).unwrap();
    let decoded: Host<Cow<'static, str>> = serde_json::from_str(&json).unwrap();
    assert_eq!(decoded.unwrap_domain().as_ref(), expected);

    let bincode = bincode::serialize(value).unwrap();
    let decoded: Host<Cow<'static, str>> = bincode::deserialize(&bincode).unwrap();
    assert_eq!(decoded.unwrap_domain().as_ref(), expected);

    let msgpack = rmp_serde::to_vec(value).unwrap();
    let decoded: Host<Cow<'static, str>> = rmp_serde::from_slice(&msgpack).unwrap();
    assert_eq!(decoded.unwrap_domain().as_ref(), expected);
  }

  fn assert_bytes_normalizes(value: &RawHost<Cow<'static, [u8]>>, expected: &[u8]) {
    let json = serde_json::to_string(value).unwrap();
    let decoded: Host<Cow<'static, [u8]>> = serde_json::from_str(&json).unwrap();
    assert_eq!(decoded.unwrap_domain().as_ref(), expected);

    let bincode = bincode::serialize(value).unwrap();
    let decoded: Host<Cow<'static, [u8]>> = bincode::deserialize(&bincode).unwrap();
    assert_eq!(decoded.unwrap_domain().as_ref(), expected);

    let msgpack = rmp_serde::to_vec(value).unwrap();
    let decoded: Host<Cow<'static, [u8]>> = rmp_serde::from_slice(&msgpack).unwrap();
    assert_eq!(decoded.unwrap_domain().as_ref(), expected);
  }

  let borrowed: Host<Cow<'static, str>> =
    Host::from(Domain::try_from(Cow::Borrowed("example.com")).unwrap());
  assert_roundtrips(&borrowed);
  let owned: Host<Cow<'static, str>> =
    Host::from(Domain::try_from(Cow::Owned(String::from("example.org"))).unwrap());
  assert_roundtrips(&owned);

  let borrowed: Host<Cow<'static, [u8]>> =
    Host::from(Domain::try_from(Cow::Borrowed(&b"example.com"[..])).unwrap());
  assert_roundtrips(&borrowed);
  let owned: Host<Cow<'static, [u8]>> =
    Host::from(Domain::try_from(Cow::Owned(Vec::from(&b"example.org"[..]))).unwrap());
  assert_roundtrips(&owned);

  for (input, expected) in [
    ("测试.中国", "xn--0zwm56d.xn--fiqs8s"),
    ("example%2Ecom", "example.com"),
  ] {
    assert_str_normalizes(&RawHost::Domain(Cow::Borrowed(input)), expected);
    assert_bytes_normalizes(
      &RawHost::Domain(Cow::Borrowed(input.as_bytes())),
      expected.as_bytes(),
    );
  }

  let invalid = RawHost::Domain(Cow::Borrowed(""));
  assert_rejected::<Host<Cow<'static, str>>, _>(&invalid);
  let invalid: RawHost<Cow<'static, str>> =
    RawHost::Domain(Cow::Owned(String::from("example.123")));
  assert_rejected::<Host<Cow<'static, str>>, _>(&invalid);
  let invalid = RawHost::Domain(Cow::Borrowed(&[0xff][..]));
  assert_rejected::<Host<Cow<'static, [u8]>>, _>(&invalid);
  let invalid: RawHost<Cow<'static, [u8]>> =
    RawHost::Domain(Cow::Owned(Vec::from(&b"-example.com"[..])));
  assert_rejected::<Host<Cow<'static, [u8]>>, _>(&invalid);
}

#[cfg(any(feature = "std", feature = "alloc"))]
#[test]
fn host_domain_equality_ordering_and_hash_follow_storage_representation() {
  let lower: Host<String> = Host::try_from("example.com").unwrap();
  let upper: Host<String> = Host::try_from("EXAMPLE.COM").unwrap();
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

  let fqdn: Host<String> = Host::try_from("EXAMPLE.COM.").unwrap();
  assert_ne!(upper, fqdn);

  let ip_lower = Host::<String>::from_ip("127.0.0.1".parse().unwrap());
  let ip_upper = Host::<String>::from_ip("127.0.0.1".parse().unwrap());
  assert_eq!(ip_lower, ip_upper);
}
