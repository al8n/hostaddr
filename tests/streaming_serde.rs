#![cfg(feature = "serde")]

use std::io::Cursor;

use hostaddr::Buffer;
use serde::Deserialize;

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
fn buffer_deserializes_owned_legacy_string_visitors() {
  let deserializer =
    serde::de::value::StringDeserializer::<serde::de::value::Error>::new("测试.中国".to_owned());
  let buffer = Buffer::deserialize(deserializer).unwrap();
  assert_eq!(buffer.as_str(), "xn--0zwm56d.xn--fiqs8s");
}

#[test]
fn buffer_deserializes_owned_binary_values() {
  let encoded = bincode::serialize(&b"example.com".as_slice()).unwrap();
  let buffer: Buffer = bincode::deserialize(&encoded).unwrap();
  assert_eq!(buffer.as_bytes(), b"example.com");
}
