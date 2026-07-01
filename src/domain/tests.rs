use super::*;

#[test]
fn negative_try_from_ascii_bytes() {
  let err = Domain::<[u8]>::try_from_ascii_bytes("测试.中国".as_bytes()).unwrap_err();
  assert_eq!(err.as_str(), "invalid ASCII domain");
  let err = Domain::<[u8]>::try_from_ascii_bytes("@example.com".as_bytes()).unwrap_err();
  assert_eq!(err.as_str(), "invalid ASCII domain");
}

#[test]
fn negative_try_from_ascii_str() {
  let err = Domain::<str>::try_from_ascii_str("测试.中国").unwrap_err();
  assert_eq!(err.as_str(), "invalid ASCII domain");
  let err = Domain::<str>::try_from_ascii_str("@example.com").unwrap_err();
  assert_eq!(err.as_str(), "invalid ASCII domain");
}

/// Regression test: verify_ascii_domain must enforce the 253-byte max length
/// (254 with trailing dot for FQDN). Previously, domains > 254 bytes were accepted.
#[test]
#[cfg(feature = "std")]
fn domain_length_boundary() {
  // Helper to build a domain of exact length from 50-byte labels
  fn make_domain(label_lens: &[usize]) -> std::string::String {
    label_lens
      .iter()
      .enumerate()
      .map(|(i, &len)| std::string::String::from_utf8(vec![b'a' + (i as u8 % 26); len]).unwrap())
      .collect::<std::vec::Vec<_>>()
      .join(".")
  }

  // 253 bytes: valid
  let d253 = make_domain(&[50, 50, 50, 50, 49]);
  assert_eq!(d253.len(), 253);
  assert!(verify_ascii_domain(d253.as_bytes()).is_ok());

  // 254 bytes with trailing dot (FQDN): valid
  let d254_fqdn = std::format!("{}.", d253);
  assert_eq!(d254_fqdn.len(), 254);
  assert!(verify_ascii_domain(d254_fqdn.as_bytes()).is_ok());

  // 254 bytes without trailing dot: invalid
  let d254 = make_domain(&[50, 50, 50, 50, 50]);
  assert_eq!(d254.len(), 254);
  assert!(verify_ascii_domain(d254.as_bytes()).is_err());

  // 255 bytes: invalid
  let d255 = make_domain(&[50, 50, 50, 50, 51]);
  assert_eq!(d255.len(), 255);
  assert!(verify_ascii_domain(d255.as_bytes()).is_err());

  // 300 bytes: invalid
  let d300 = make_domain(&[50, 50, 50, 50, 50, 45]);
  assert_eq!(d300.len(), 300);
  assert!(verify_ascii_domain(d300.as_bytes()).is_err());
}
