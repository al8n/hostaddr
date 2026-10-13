#![cfg(feature = "serde")]

use core::{
  fmt::Debug,
  net::{IpAddr, SocketAddr, SocketAddrV6},
};

#[cfg(any(feature = "alloc", feature = "std"))]
use hostaddr::{Addr, Buffer, Domain, Host, HostAddr, LocalAddr};
#[cfg(unix)]
use hostaddr::{IpcAddr, UnixAddr};
use hostaddr::{LinkLocalAddr, LoopbackAddr, LoopbackIpAddr};
use serde::{
  de::DeserializeOwned,
  ser::{Error as SerdeError, Impossible, SerializeTupleVariant, Serializer},
  Serialize,
};
use serde_test2::{
  assert_de_tokens_error, assert_ser_tokens, assert_tokens, Compact, Configure, Token,
};

#[derive(Debug)]
struct VariantIndexError;

impl core::fmt::Display for VariantIndexError {
  fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    formatter.write_str("unsupported serializer shape")
  }
}

impl std::error::Error for VariantIndexError {}

impl SerdeError for VariantIndexError {
  fn custom<T>(_: T) -> Self
  where
    T: core::fmt::Display,
  {
    Self
  }
}

struct VariantIndexSerializer<'a> {
  index: &'a mut Option<u32>,
}

struct VariantIndexTupleVariant;

impl SerializeTupleVariant for VariantIndexTupleVariant {
  type Ok = ();
  type Error = VariantIndexError;

  fn serialize_field<T>(&mut self, _: &T) -> Result<(), Self::Error>
  where
    T: ?Sized + Serialize,
  {
    Ok(())
  }

  fn end(self) -> Result<Self::Ok, Self::Error> {
    Ok(())
  }
}

macro_rules! reject_variant_index_serializer_methods {
  ($($name:ident($($arg:ident: $ty:ty),*) -> $ret:ty;)*) => {
    $(
      fn $name(self, $($arg: $ty),*) -> Result<$ret, Self::Error> {
        $(let _ = &$arg;)*
        Err(VariantIndexError)
      }
    )*
  };
}

impl Serializer for VariantIndexSerializer<'_> {
  type Ok = ();
  type Error = VariantIndexError;
  type SerializeSeq = Impossible<(), VariantIndexError>;
  type SerializeTuple = Impossible<(), VariantIndexError>;
  type SerializeTupleStruct = Impossible<(), VariantIndexError>;
  type SerializeTupleVariant = VariantIndexTupleVariant;
  type SerializeMap = Impossible<(), VariantIndexError>;
  type SerializeStruct = Impossible<(), VariantIndexError>;
  type SerializeStructVariant = Impossible<(), VariantIndexError>;

  fn is_human_readable(&self) -> bool {
    false
  }

  fn serialize_tuple_variant(
    self,
    _: &'static str,
    variant_index: u32,
    _: &'static str,
    _: usize,
  ) -> Result<Self::SerializeTupleVariant, Self::Error> {
    *self.index = Some(variant_index);
    Ok(VariantIndexTupleVariant)
  }

  fn collect_str<T>(self, _: &T) -> Result<Self::Ok, Self::Error>
  where
    T: ?Sized + core::fmt::Display,
  {
    Err(VariantIndexError)
  }

  fn serialize_some<T>(self, _: &T) -> Result<Self::Ok, Self::Error>
  where
    T: ?Sized + Serialize,
  {
    Err(VariantIndexError)
  }

  fn serialize_newtype_struct<T>(self, _: &'static str, _: &T) -> Result<Self::Ok, Self::Error>
  where
    T: ?Sized + Serialize,
  {
    Err(VariantIndexError)
  }

  fn serialize_newtype_variant<T>(
    self,
    _: &'static str,
    _: u32,
    _: &'static str,
    _: &T,
  ) -> Result<Self::Ok, Self::Error>
  where
    T: ?Sized + Serialize,
  {
    Err(VariantIndexError)
  }

  reject_variant_index_serializer_methods! {
    serialize_bool(value: bool) -> ();
    serialize_i8(value: i8) -> ();
    serialize_i16(value: i16) -> ();
    serialize_i32(value: i32) -> ();
    serialize_i64(value: i64) -> ();
    serialize_i128(value: i128) -> ();
    serialize_u8(value: u8) -> ();
    serialize_u16(value: u16) -> ();
    serialize_u32(value: u32) -> ();
    serialize_u64(value: u64) -> ();
    serialize_u128(value: u128) -> ();
    serialize_f32(value: f32) -> ();
    serialize_f64(value: f64) -> ();
    serialize_char(value: char) -> ();
    serialize_str(value: &str) -> ();
    serialize_bytes(value: &[u8]) -> ();
    serialize_none() -> ();
    serialize_unit() -> ();
    serialize_unit_struct(name: &'static str) -> ();
    serialize_unit_variant(name: &'static str, variant_index: u32, variant: &'static str) -> ();
    serialize_seq(len: Option<usize>) -> Impossible<(), VariantIndexError>;
    serialize_tuple(len: usize) -> Impossible<(), VariantIndexError>;
    serialize_tuple_struct(name: &'static str, len: usize) -> Impossible<(), VariantIndexError>;
    serialize_map(len: Option<usize>) -> Impossible<(), VariantIndexError>;
    serialize_struct(name: &'static str, len: usize) -> Impossible<(), VariantIndexError>;
    serialize_struct_variant(name: &'static str, variant_index: u32, variant: &'static str, len: usize) -> Impossible<(), VariantIndexError>;
  }
}

fn assert_semantic_variant_index<T: Serialize>(value: &T, expected: u32) {
  let mut index = None;
  value
    .serialize(VariantIndexSerializer { index: &mut index })
    .unwrap();
  assert_eq!(index, Some(expected));
}

fn assert_wire<T>(value: &T, json: &str)
where
  T: Serialize + DeserializeOwned + Debug + PartialEq,
{
  assert_eq!(serde_json::to_string(value).unwrap(), json);
  assert_eq!(serde_json::from_str::<T>(json).unwrap(), *value);
  let msgpack = rmp_serde::to_vec(value).unwrap();
  assert_eq!(rmp_serde::from_slice::<T>(&msgpack).unwrap(), *value);
}

#[cfg(any(feature = "alloc", feature = "std"))]
#[test]
fn serde_tokens_freeze_text_and_binary_domain_shapes() {
  let domain = Domain::<String>::try_from("example.com").unwrap();
  assert_tokens(&domain.clone().readable(), &[Token::Str("example.com")]);
  assert_tokens(&domain.compact(), &[Token::Str("example.com")]);

  let buffer = Domain::<Buffer>::try_from("example.com")
    .unwrap()
    .into_inner();
  assert_tokens(&buffer.readable(), &[Token::Str("example.com")]);
  assert_tokens(&buffer.compact(), &[Token::Bytes(b"example.com")]);
}

#[cfg(any(feature = "alloc", feature = "std"))]
#[test]
fn rc1_domain_host_and_hostaddr_wire_is_frozen() {
  let domain = Domain::<String>::try_from("example.com").unwrap();
  assert_wire(&domain, "\"example.com\"");

  let buffer = Domain::<Buffer>::try_from("example.com")
    .unwrap()
    .into_inner();
  assert_wire(&buffer, "\"example.com\"");

  let host = Host::<String>::try_from("example.com").unwrap();
  assert_wire(&host, r#"{"domain":"example.com"}"#);

  let host = Host::<String>::from_ip("127.0.0.1".parse().unwrap());
  assert_wire(&host, r#"{"ip":"127.0.0.1"}"#);

  let domain_host = Host::<String>::try_from("example.com").unwrap();
  assert_ser_tokens(
    &domain_host.clone().readable(),
    &[
      Token::NewtypeVariant {
        name: "Host",
        variant: "domain",
      },
      Token::Str("example.com"),
    ],
  );
  assert_ser_tokens(
    &domain_host.compact(),
    &[
      Token::NewtypeVariant {
        name: "Host",
        variant: "domain",
      },
      Token::Str("example.com"),
    ],
  );

  let addr = HostAddr::<String>::try_from("example.com:443").unwrap();
  assert_wire(&addr, r#"{"host":{"domain":"example.com"},"port":443}"#);
  assert_ser_tokens(
    &addr.clone().readable(),
    &[
      Token::Struct {
        name: "HostAddr",
        len: 2,
      },
      Token::Str("host"),
      Token::NewtypeVariant {
        name: "Host",
        variant: "domain",
      },
      Token::Str("example.com"),
      Token::Str("port"),
      Token::Some,
      Token::U16(443),
      Token::StructEnd,
    ],
  );
  assert_ser_tokens(
    &addr.compact(),
    &[
      Token::Struct {
        name: "HostAddr",
        len: 2,
      },
      Token::Str("host"),
      Token::NewtypeVariant {
        name: "Host",
        variant: "domain",
      },
      Token::Str("example.com"),
      Token::Str("port"),
      Token::Some,
      Token::U16(443),
      Token::StructEnd,
    ],
  );

  let addr = HostAddr::<String>::from(("127.0.0.1".parse::<IpAddr>().unwrap(), 8080));
  assert_wire(&addr, r#"{"host":{"ip":"127.0.0.1"},"port":8080}"#);
}

#[test]
fn semantic_ip_and_socket_wire_is_frozen_and_backward_compatible() {
  let ip = LoopbackIpAddr::try_from("127.0.0.1".parse::<IpAddr>().unwrap()).unwrap();
  assert_wire(&ip, "\"127.0.0.1\"");

  let v4 = LoopbackAddr::try_from("127.0.0.1:8080".parse::<SocketAddr>().unwrap()).unwrap();
  assert_wire(&v4, r#"{"v4":{"ip":"127.0.0.1","port":8080}}"#);
  assert_semantic_variant_index(&v4, 0);
  assert_tokens(
    &v4.readable(),
    &[
      Token::StructVariant {
        name: "HumanSocketAddr",
        variant: "v4",
        len: 2,
      },
      Token::Str("ip"),
      Token::Str("127.0.0.1"),
      Token::Str("port"),
      Token::U16(8080),
      Token::StructVariantEnd,
    ],
  );
  assert_tokens(
    &v4.compact(),
    &[
      Token::TupleVariant {
        name: "BinarySocketAddr",
        variant: "V4",
        len: 2,
      },
      Token::Tuple { len: 4 },
      Token::U8(127),
      Token::U8(0),
      Token::U8(0),
      Token::U8(1),
      Token::TupleEnd,
      Token::U16(8080),
      Token::TupleVariantEnd,
    ],
  );
  let rc1_msgpack = rmp_serde::to_vec(&v4.as_socket_addr()).unwrap();
  assert_eq!(rmp_serde::to_vec(&v4).unwrap(), rc1_msgpack);
  assert_eq!(
    rmp_serde::from_slice::<LoopbackAddr>(&rc1_msgpack).unwrap(),
    v4
  );
  assert_eq!(
    serde_json::from_str::<LoopbackAddr>("\"127.0.0.1:8080\"").unwrap(),
    v4
  );

  let v6 = LoopbackAddr::try_from("[::1]:443".parse::<SocketAddr>().unwrap()).unwrap();
  assert_wire(
    &v6,
    r#"{"v6":{"ip":"::1","port":443,"flowinfo":0,"scope_id":0}}"#,
  );
  assert_semantic_variant_index(&v6, 1);
  assert_tokens(
    &v6.compact(),
    &[
      Token::TupleVariant {
        name: "BinarySocketAddr",
        variant: "V6",
        len: 2,
      },
      Token::Tuple { len: 16 },
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(1),
      Token::TupleEnd,
      Token::U16(443),
      Token::TupleVariantEnd,
    ],
  );
  let rc1_msgpack = rmp_serde::to_vec(&v6.as_socket_addr()).unwrap();
  assert_eq!(rmp_serde::to_vec(&v6).unwrap(), rc1_msgpack);
  assert_eq!(
    rmp_serde::from_slice::<LoopbackAddr>(&rc1_msgpack).unwrap(),
    v6
  );
  assert_eq!(
    serde_json::from_str::<LoopbackAddr>("\"[::1]:443\"").unwrap(),
    v6
  );

  let scoped =
    LinkLocalAddr::try_from(SocketAddrV6::new("fe80::1".parse().unwrap(), 443, 7, 42)).unwrap();
  assert_semantic_variant_index(&scoped, 2);
  assert_wire(
    &scoped,
    r#"{"v6":{"ip":"fe80::1","port":443,"flowinfo":7,"scope_id":42}}"#,
  );
  assert_tokens(
    &scoped.compact(),
    &[
      Token::TupleVariant {
        name: "BinarySocketAddr",
        variant: "V6Extended",
        len: 4,
      },
      Token::Tuple { len: 16 },
      Token::U8(0xfe),
      Token::U8(0x80),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(1),
      Token::TupleEnd,
      Token::U16(443),
      Token::U32(7),
      Token::U32(42),
      Token::TupleVariantEnd,
    ],
  );
  // This literal freezes rmp-serde's name-based compact representation and
  // all V6Extended fields; numeric variant indices are asserted separately.
  const V6_EXTENDED_MSGPACK: &[u8] = &[
    129, 170, 86, 54, 69, 120, 116, 101, 110, 100, 101, 100, 148, 220, 0, 16, 204, 254, 204, 128,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 205, 1, 187, 7, 42,
  ];
  assert_eq!(rmp_serde::to_vec(&scoped).unwrap(), V6_EXTENDED_MSGPACK);
  assert_eq!(
    rmp_serde::from_slice::<LinkLocalAddr>(V6_EXTENDED_MSGPACK).unwrap(),
    scoped
  );

  assert_de_tokens_error::<Compact<LoopbackAddr>>(
    &[
      Token::TupleVariant {
        name: "BinarySocketAddr",
        variant: "V4",
        len: 2,
      },
      Token::Tuple { len: 4 },
      Token::U8(192),
      Token::U8(0),
      Token::U8(2),
      Token::U8(1),
      Token::TupleEnd,
      Token::U16(80),
      Token::TupleVariantEnd,
    ],
    "not a loopback socket address",
  );
  assert_de_tokens_error::<Compact<LoopbackAddr>>(
    &[
      Token::TupleVariant {
        name: "BinarySocketAddr",
        variant: "V6",
        len: 2,
      },
      Token::Tuple { len: 16 },
      Token::U8(0x20),
      Token::U8(0x01),
      Token::U8(0x0d),
      Token::U8(0xb8),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(1),
      Token::TupleEnd,
      Token::U16(80),
      Token::TupleVariantEnd,
    ],
    "not a loopback socket address",
  );
  // The V6Extended token fixture covers its four-field shape; the numeric
  // variant index is asserted separately through VariantIndexSerializer.
  assert_de_tokens_error::<Compact<LoopbackAddr>>(
    &[
      Token::TupleVariant {
        name: "BinarySocketAddr",
        variant: "V6Extended",
        len: 4,
      },
      Token::Tuple { len: 16 },
      Token::U8(0x20),
      Token::U8(0x01),
      Token::U8(0x0d),
      Token::U8(0xb8),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(0),
      Token::U8(1),
      Token::TupleEnd,
      Token::U16(80),
      Token::U32(7),
      Token::U32(42),
      Token::TupleVariantEnd,
    ],
    "not a loopback socket address",
  );

  assert!(serde_json::from_str::<LoopbackAddr>("\"192.0.2.1:80\"").is_err());
  assert!(serde_json::from_str::<LoopbackAddr>("\"[2001:db8::1]:80\"").is_err());
}

#[cfg(any(feature = "alloc", feature = "std"))]
#[test]
fn aggregate_address_wire_is_literal_and_accepts_rc1_semantic_json() {
  let host = HostAddr::<String>::try_from("example.com:443").unwrap();
  let addr: Addr<String, String, Vec<u8>> = host.into();
  assert_wire(
    &addr,
    r#"{"host":{"host":{"domain":"example.com"},"port":443}}"#,
  );

  let loopback = LoopbackAddr::try_from("127.0.0.1:8080".parse::<SocketAddr>().unwrap()).unwrap();
  let local: LocalAddr<String, Vec<u8>> = loopback.into();
  assert_wire(
    &local,
    r#"{"loopback":{"v4":{"ip":"127.0.0.1","port":8080}}}"#,
  );
  assert_eq!(
    serde_json::from_str::<LocalAddr<String, Vec<u8>>>(r#"{"loopback":"127.0.0.1:8080"}"#,)
      .unwrap(),
    local
  );
}

#[cfg(unix)]
#[test]
fn ipc_wire_is_literal() {
  let ipc: IpcAddr<String, Vec<u8>> = UnixAddr::new(String::from("/tmp/app.sock")).into();
  assert_wire(&ipc, r#"["unix","/tmp/app.sock"]"#);
}
