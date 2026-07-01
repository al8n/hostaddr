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

#[test]
fn domain_core_accessors_and_ascii_branches() {
  use core::borrow::Borrow;

  assert_eq!(ParseDomainError(()).as_str(), "invalid domain");
  assert_eq!(ParseAsciiDomainError(()).as_str(), "invalid ASCII domain");

  let nested = Domain(Domain("example.com"));
  assert_eq!(nested.flatten().as_inner(), &"example.com");
  let nested = Domain(Domain("example.org"));
  assert_eq!(nested.flatten_const().as_inner(), &"example.org");

  let unchecked = Domain::new_unchecked("example.net");
  assert_eq!(unchecked.as_inner(), &"example.net");
  assert_eq!(unchecked.into_inner(), "example.net");

  let borrowed = Domain::<str>::from_ref_unchecked("example.io");
  assert_eq!(borrowed.as_inner(), "example.io");
  let copied = Domain::new_unchecked("example.io").as_ref().copied();
  assert_eq!(copied.into_inner(), "example.io");
  assert_eq!(borrowed.as_bytes().as_str().as_inner(), "example.io");

  let borrowed_bytes = Domain::<[u8]>::try_from_ascii_bytes(b"example.dev").unwrap();
  assert_eq!(
    borrowed_bytes.as_str().as_bytes().as_inner(),
    b"example.dev"
  );
  assert_eq!(Borrow::<[u8]>::borrow(borrowed_bytes), b"example.dev");

  let bytes_as_ref: &[u8] = AsRef::<[u8]>::as_ref(borrowed_bytes);
  assert_eq!(bytes_as_ref, b"example.dev");
  let str_as_ref: &str = AsRef::<str>::as_ref(borrowed);
  assert_eq!(str_as_ref, "example.io");

  let fqdn = Domain::<str>::try_from_ascii_str("example.com").unwrap();
  assert!(!fqdn.is_fqdn());
  assert_eq!(fqdn.to_fqdn().unwrap().as_inner().as_str(), "example.com.");
  let already_fqdn = Domain::<str>::try_from_ascii_str("example.com.").unwrap();
  assert!(already_fqdn.is_fqdn());
  assert!(already_fqdn.to_fqdn().is_none());

  assert!(verify_ascii_domain(b"").is_err());
  assert!(verify_ascii_domain(b".").is_ok());
  assert!(verify_ascii_domain(b"example..com").is_err());
  assert!(verify_ascii_domain(b"example-.com").is_err());
  assert!(verify_ascii_domain(b"example.123").is_err());
  assert!(verify_ascii_domain(b"example.com.").is_ok());
}

#[cfg(any(feature = "std", feature = "alloc"))]
#[test]
fn domain_owned_conversions_cover_storage_variants() {
  use std::{
    borrow::{Borrow, Cow},
    boxed::Box,
    rc::Rc,
    string::String,
    sync::Arc,
    vec::Vec,
  };

  let domain: Domain<String> = Domain::try_from("example.com").unwrap();
  assert_eq!(domain.as_ref().cloned().into_inner(), "example.com");
  assert_eq!(*domain.as_deref().as_inner(), "example.com");
  assert_eq!(Borrow::<String>::borrow(&domain).as_str(), "example.com");
  assert_eq!(AsRef::<str>::as_ref(&domain), "example.com");
  assert_eq!(AsRef::<[u8]>::as_ref(&domain), b"example.com");

  let original = String::from("example.com");
  let owned_from_ref = Domain::<String>::try_from(&original).unwrap();
  assert_eq!(owned_from_ref.as_inner(), "example.com");
  let owned_from_value = Domain::<String>::try_from(original).unwrap();
  assert_eq!(owned_from_value.as_inner(), "example.com");

  let idna: Domain<String> = Domain::try_from("测试.中国").unwrap();
  assert_eq!(idna.as_inner(), "xn--0zwm56d.xn--fiqs8s");
  let percent: Domain<String> = Domain::try_from("example%2Ecom").unwrap();
  assert_eq!(percent.as_inner(), "example.com");

  let from_bytes: Domain<Vec<u8>> = Domain::try_from(b"example.com".as_slice()).unwrap();
  assert_eq!(from_bytes.as_inner().as_slice(), b"example.com");
  let vec_bytes = Vec::from(b"example.com".as_slice());
  let from_vec_ref = Domain::<Vec<u8>>::try_from(&vec_bytes).unwrap();
  assert_eq!(from_vec_ref.as_inner().as_slice(), b"example.com");
  let from_vec_value = Domain::<Vec<u8>>::try_from(vec_bytes).unwrap();
  assert_eq!(from_vec_value.as_inner().as_slice(), b"example.com");

  let idna_value = String::from("测试.中国");
  let idna_owned = Domain::<String>::try_from(idna_value).unwrap();
  assert_eq!(idna_owned.as_inner(), "xn--0zwm56d.xn--fiqs8s");
  let idna_ref = String::from("测试.中国");
  let idna_owned_from_ref = Domain::<String>::try_from(&idna_ref).unwrap();
  assert_eq!(idna_owned_from_ref.as_inner(), "xn--0zwm56d.xn--fiqs8s");

  let percent_idna = Domain::try_from_bytes("测试%2E中国".as_bytes()).unwrap();
  assert_eq!(
    percent_idna.unwrap_right().as_str(),
    "xn--0zwm56d.xn--fiqs8s"
  );

  let cow_str: Domain<Cow<'_, str>> = Domain::try_from("example.com").unwrap();
  assert!(matches!(cow_str.into_inner(), Cow::Borrowed("example.com")));
  let cow_bytes: Domain<Cow<'_, [u8]>> = Domain::try_from(b"example.com".as_slice()).unwrap();
  assert!(matches!(
    cow_bytes.into_inner(),
    Cow::Borrowed(b"example.com")
  ));

  let arc_str: Domain<Arc<str>> = Domain::try_from("example.com").unwrap();
  assert_eq!(arc_str.as_inner().as_ref(), "example.com");
  let box_str: Domain<Box<str>> = Domain::try_from("example.com").unwrap();
  assert_eq!(box_str.as_inner().as_ref(), "example.com");
  let rc_str: Domain<Rc<str>> = Domain::try_from("example.com").unwrap();
  assert_eq!(rc_str.as_inner().as_ref(), "example.com");
  let arc_bytes: Domain<Arc<[u8]>> = Domain::try_from(b"example.com".as_slice()).unwrap();
  assert_eq!(arc_bytes.as_inner().as_ref(), b"example.com");
  let box_bytes: Domain<Box<[u8]>> = Domain::try_from(b"example.com".as_slice()).unwrap();
  assert_eq!(box_bytes.as_inner().as_ref(), b"example.com");
  let rc_bytes: Domain<Rc<[u8]>> = Domain::try_from(b"example.com".as_slice()).unwrap();
  assert_eq!(rc_bytes.as_inner().as_ref(), b"example.com");

  let from_str_ref: Domain<Buffer> = Domain::<str>::try_from_ascii_str("example.com")
    .unwrap()
    .into();
  assert_eq!(from_str_ref.as_inner().as_str(), "example.com");
  let from_bytes_ref: Domain<Buffer> = Domain::<[u8]>::try_from_ascii_bytes(b"example.com")
    .unwrap()
    .into();
  assert_eq!(from_bytes_ref.as_inner().as_bytes(), b"example.com");
  let from_domain_str: Domain<Buffer> = Domain::<str>::try_from_ascii_str("example.com")
    .unwrap()
    .as_ref()
    .into();
  assert_eq!(from_domain_str.as_inner().as_str(), "example.com");
  let from_domain_bytes: Domain<Buffer> = Domain::<[u8]>::try_from_ascii_bytes(b"example.com")
    .unwrap()
    .as_ref()
    .into();
  assert_eq!(from_domain_bytes.as_inner().as_bytes(), b"example.com");

  let buffer: Buffer = from_domain_str.into();
  let from_buffer: Domain<Buffer> = buffer.into();
  assert_eq!(from_buffer.as_inner().as_str(), "example.com");
  let from_buffer_to_string: Domain<String> = from_buffer.into();
  assert_eq!(from_buffer_to_string.as_inner(), "example.com");
  let from_buffer_ref = Domain::from(Buffer::copy_from_str("example.com"));
  let from_buffer_ref_to_string: Domain<String> = (&from_buffer_ref).into();
  assert_eq!(from_buffer_ref_to_string.as_inner(), "example.com");

  let buffer = Buffer::copy_from_str("example.com");
  let as_string: String = buffer.into();
  assert_eq!(as_string, "example.com");
  let buffer = Buffer::copy_from_str("example.com");
  let as_vec: Vec<u8> = buffer.into();
  assert_eq!(as_vec, b"example.com");
  let buffer = Buffer::copy_from_str("example.com");
  let as_cow_str: Cow<'_, str> = buffer.into();
  assert_eq!(as_cow_str, "example.com");
  let buffer = Buffer::copy_from_str("example.com");
  let as_cow_bytes: Cow<'_, [u8]> = buffer.into();
  assert_eq!(as_cow_bytes.as_ref(), b"example.com");

  let buffer = Buffer::copy_from_str("example.com");
  let borrowed_str: &str = (&buffer).into();
  let borrowed_bytes: &[u8] = (&buffer).into();
  assert_eq!(borrowed_str, "example.com");
  assert_eq!(borrowed_bytes, b"example.com");
  assert_eq!(Borrow::<str>::borrow(&buffer), "example.com");
  assert_eq!(AsRef::<str>::as_ref(&buffer), "example.com");
  assert_eq!(AsRef::<[u8]>::as_ref(&buffer), b"example.com");
  assert_eq!(buffer.const_as_str(), "example.com");

  let mut writable = Buffer::new();
  core::fmt::Write::write_str(&mut writable, "example").unwrap();
  core::fmt::Write::write_str(&mut writable, ".com").unwrap();
  assert_eq!(writable.as_str(), "example.com");

  let too_long = "a".repeat(255);
  assert!(core::fmt::Write::write_str(&mut Buffer::new(), &too_long).is_err());
  let mut full = Buffer::new();
  for _ in 0..254 {
    full.push(b'a').unwrap();
  }
  assert_eq!(full.push(b'b'), Err(b'b'));

  assert!(verify_domain(b"example.com").is_ok());
  assert!(verify_domain("测试.中国".as_bytes()).is_ok());
  assert!(verify_domain(b"example%2Ecom").is_ok());
  assert!(verify_domain("测试%2E中国".as_bytes()).is_ok());
  assert!(verify_domain(b"exam ple.com").is_err());

  assert!(verify_ascii_domain_allow_percent_encoding(b"example.com").is_ok());
  assert!(verify_ascii_domain_allow_percent_encoding(b"example%2Ecom").is_ok());
  assert!(verify_ascii_domain_allow_percent_encoding("测试.中国".as_bytes()).is_err());
  assert!(verify_ascii_domain_allow_percent_encoding("测试%2E中国".as_bytes()).is_err());
}

#[cfg(feature = "serde")]
#[test]
fn buffer_serde_uses_text_for_human_readable_and_bytes_for_binary() {
  let buffer = Buffer::copy_from_str("example.com");
  let json = serde_json::to_string(&buffer).unwrap();
  assert_eq!(json, "\"example.com\"");
  let decoded: Buffer = serde_json::from_str(&json).unwrap();
  assert_eq!(decoded.as_str(), "example.com");

  #[cfg(any(feature = "std", feature = "alloc"))]
  {
    let decoded: Buffer = serde_json::from_str("\"测试.中国\"").unwrap();
    assert_eq!(decoded.as_str(), "xn--0zwm56d.xn--fiqs8s");
  }

  let binary = bincode::serialize(&buffer).unwrap();
  let decoded: Buffer = bincode::deserialize(&binary).unwrap();
  assert_eq!(decoded.as_bytes(), b"example.com");

  #[cfg(any(feature = "std", feature = "alloc"))]
  {
    let binary = bincode::serialize(&"测试.中国".as_bytes()).unwrap();
    let decoded: Buffer = bincode::deserialize(&binary).unwrap();
    assert_eq!(decoded.as_str(), "xn--0zwm56d.xn--fiqs8s");
  }
}
