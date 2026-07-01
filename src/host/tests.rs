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
