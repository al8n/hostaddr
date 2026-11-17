#![cfg(feature = "serde")]

use std::io::Cursor;

use hostaddr::{Buffer, Domain};
use serde::Deserialize;
use serde_test2::{assert_de_tokens, assert_tokens, Configure, Token};

#[test]
fn buffer_deserializes_borrowed_json_strings() {
  let buffer: Buffer = serde_json::from_str("\"example.com\"").unwrap();
  assert_eq!(buffer.as_str(), "example.com");
}

#[test]
fn buffer_deserializes_transient_strings_from_reader() {
  let mut deserializer =
    serde_json::Deserializer::from_reader(Cursor::new(br#""xn--0zwm56d.xn--fiqs8s""#));
  let buffer = Buffer::deserialize(&mut deserializer).unwrap();
  assert_eq!(buffer.as_str(), "xn--0zwm56d.xn--fiqs8s");
}

#[test]
fn buffer_deserializes_owned_ascii_string_visitors() {
  let deserializer =
    serde::de::value::StringDeserializer::<serde::de::value::Error>::new("example.com".to_owned());
  let buffer = Buffer::deserialize(deserializer).unwrap();
  assert_eq!(buffer.as_str(), "example.com");
}

#[cfg(any(feature = "alloc", feature = "std"))]
#[test]
fn buffer_deserializes_owned_unicode_string_visitors_with_idna() {
  let deserializer =
    serde::de::value::StringDeserializer::<serde::de::value::Error>::new("测试.中国".to_owned());
  let buffer = Buffer::deserialize(deserializer).unwrap();
  assert_eq!(buffer.as_str(), "xn--0zwm56d.xn--fiqs8s");
}

#[test]
fn buffer_deserializes_owned_binary_values() {
  let buffer = Domain::<Buffer>::try_from("example.com")
    .unwrap()
    .into_inner();
  assert_tokens(&buffer.compact(), &[Token::Bytes(b"example.com")]);
  let compact = buffer.compact();
  assert_de_tokens(&compact, &[Token::BorrowedBytes(b"example.com")]);
  assert_de_tokens(&compact, &[Token::Bytes(b"example.com")]);
  assert_de_tokens(&compact, &[Token::ByteBuf(b"example.com")]);
  assert_eq!(buffer.as_bytes(), b"example.com");
}
