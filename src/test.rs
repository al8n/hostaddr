use super::*;

use std::{borrow::Cow, boxed::Box, rc::Rc, sync::Arc};

#[cfg(feature = "smol_str_0_3")]
use smol_str_0_3::SmolStr;

#[cfg(feature = "triomphe_0_1")]
use triomphe_0_1::Arc as TriompheArc;

#[cfg(feature = "bytes_1")]
use bytes_1::Bytes;

#[cfg(feature = "tinyvec_1")]
use tinyvec_1::TinyVec;

#[cfg(feature = "smallvec_1")]
use smallvec_1::SmallVec;

static TESTS: &[(&str, bool)] = &[
    ("", false),
    (".", true),
    ("localhost", true),
    ("LOCALHOST", true),
    (".localhost", false),
    ("..localhost", false),
    ("1.2.3.4", false),
    ("127.0.0.1", false),
    ("absolute.", true),
    ("absolute..", false),
    ("multiple.labels.absolute.", true),
    ("foo.bar.com", true),
    ("infix-hyphen-allowed.com", true),
    ("-prefixhypheninvalid.com", false),
    ("suffixhypheninvalid--", false),
    ("suffixhypheninvalid-.com", false),
    ("foo.lastlabelendswithhyphen-", false),
    ("infix_underscore_allowed.com", true),
    ("_prefixunderscorevalid.com", true),
    ("labelendswithnumber1.bar.com", true),
    ("xn--bcher-kva.example", true),
    (
      "sixtythreesixtythreesixtythreesixtythreesixtythreesixtythreesix.com",
      true,
    ),
    (
      "sixtyfoursixtyfoursixtyfoursixtyfoursixtyfoursixtyfoursixtyfours.com",
      false,
    ),
    (
      "012345678901234567890123456789012345678901234567890123456789012.com",
      true,
    ),
    (
      "0123456789012345678901234567890123456789012345678901234567890123.com",
      false,
    ),
    (
      "01234567890123456789012345678901234567890123456789012345678901-.com",
      false,
    ),
    (
      "012345678901234567890123456789012345678901234567890123456789012-.com",
      false,
    ),
    ("numeric-only-final-label.1", false),
    ("numeric-only-final-label.absolute.1.", false),
    ("1starts-with-number.com", true),
    ("1Starts-with-number.com", true),
    ("-example.com", false),
    ("example-.com", false),
    ("example..com", false),
    ("example.-com", false),
    ("1.2.3.4.com", true),
    ("123.numeric-only-first-label", true),
    ("a123b.com", true),
    ("numeric-only-middle-label.4.com", true),
    ("1000-sans.badssl.com", true),
    (
      "twohundredandfiftythreecharacters.twohundredandfiftythreecharacters.twohundredandfiftythreecharacters.twohundredandfiftythreecharacters.twohundredandfiftythreecharacters.twohundredandfiftythreecharacters.twohundredandfiftythreecharacters.twohundredandfi",
      true,
    ),
    ("123.", false),
    (
      "twohundredandfiftyfourcharacters.twohundredandfiftyfourcharacters.twohundredandfiftyfourcharacters.twohundredandfiftyfourcharacters.twohundredandfiftyfourcharacters.twohundredandfiftyfourcharacters.twohundredandfiftyfourcharacters.twohundredandfiftyfourc",
      false,
    ),
    ("abc@abc.com", false),
    ("测试.com", true),
    ("测试.中国", true),
    ("测试.中国.", true),
    ("测试@测试.中国", false),
    ("example.123", false),
  ];

fn validation_try_from_str<'a, S>()
where
  Domain<S>: TryFrom<&'a str>,
{
  for (input, expected) in TESTS {
    #[cfg(any(feature = "std", feature = "alloc"))]
    println!("test: {:?} expected valid? {:?}", input, expected);
    let name = Domain::<S>::try_from(input);
    assert_eq!(*expected, name.is_ok());
  }
}

fn validation_try_from_bytes<'a, S>()
where
  Domain<S>: TryFrom<&'a [u8]>,
{
  for (input, expected) in TESTS {
    #[cfg(any(feature = "std", feature = "alloc"))]
    println!("test: {:?} expected valid? {:?}", input, expected);
    let name = Domain::<S>::try_from(input.as_bytes());
    assert_eq!(*expected, name.is_ok());
  }
}

macro_rules! gen_test_validation {
  ($($ty:ident), +$(,)?) => {
    paste::paste! {
      $(
        #[test]
        fn [<test_ $ty:snake _validation_try_from_str>]() {
          validation_try_from_str::<$ty>();
        }

        #[test]
        fn [<test_ $ty:snake _validation_try_from_bytes>]() {
          validation_try_from_bytes::<$ty>();
        }
      )*
    }
  };
}

type RcBytes = Rc<[u8]>;
type ArcBytes = Arc<[u8]>;
type BoxBytes = Box<[u8]>;
type RcStr = Rc<str>;
type ArcStr = Arc<str>;
type BoxStr = Box<str>;
type VecBytes = Vec<u8>;

#[cfg(feature = "triomphe_0_1")]
type TriompheArcStr = TriompheArc<str>;
#[cfg(feature = "triomphe_0_1")]
type TriompheArcBytes = TriompheArc<[u8]>;

#[cfg(feature = "tinyvec_1")]
type TinyBytes = TinyVec<[u8; 24]>;

#[cfg(feature = "smallvec_1")]
type SmallBytes = SmallVec<[u8; 24]>;

#[cfg(feature = "triomphe_0_1")]
gen_test_validation!(TriompheArcBytes, TriompheArcStr,);

#[cfg(feature = "smol_str_0_3")]
gen_test_validation!(SmolStr);

#[cfg(feature = "bytes_1")]
gen_test_validation!(Bytes);

#[cfg(feature = "tinyvec_1")]
gen_test_validation!(TinyBytes);

#[cfg(feature = "smallvec_1")]
gen_test_validation!(SmallBytes);

gen_test_validation!(String, RcStr, ArcStr, BoxStr, VecBytes, RcBytes, ArcBytes, BoxBytes, Buffer);

#[test]
fn test_cow_str() {
  validation_try_from_str::<Cow<'_, str>>();
}

#[test]
fn test_cow_bytes() {
  validation_try_from_bytes::<Cow<'_, [u8]>>();
}

#[test]
fn test_basic() {
  let name = Domain::try_from(&"localhost".to_string()).unwrap();
  assert_eq!("localhost", name.as_deref().into_inner());
  assert_eq!("localhost", *name.as_deref().as_inner());
  let err = ParseDomainError(());
  println!("{}", err);
}

macro_rules! gen_quickcheck {
  ($($ty:ident), +$(,)?) => {
    paste::paste! {
      $(
        #[cfg(feature = "serde")]
        #[quickcheck_macros::quickcheck]
        fn [< fuzzy_serde_host_human_readable_ $ty:snake>](node: Host<$ty>) -> bool {
          let serialized = serde_json::to_string(&node).unwrap();
          let deserialized: Host<$ty> = serde_json::from_str(&serialized).unwrap();
          node == deserialized
        }

        #[cfg(feature = "serde")]
        #[quickcheck_macros::quickcheck]
        fn [< fuzzy_serde_host_human_unreadable_ $ty:snake>](node: Host<$ty>) -> bool {
          let serialized = rmp_serde::to_vec(&node).unwrap();
          let deserialized: Host<$ty> = rmp_serde::from_slice(&serialized).unwrap();
          node == deserialized
        }

        #[cfg(feature = "serde")]
        #[quickcheck_macros::quickcheck]
        fn [< fuzzy_serde_host_addr_human_readable_ $ty:snake>](node: HostAddr<$ty>) -> bool {
          let serialized = serde_json::to_string(&node).unwrap();
          let deserialized: HostAddr<$ty> = serde_json::from_str(&serialized).unwrap();
          node == deserialized
        }

        #[cfg(feature = "serde")]
        #[quickcheck_macros::quickcheck]
        fn [< fuzzy_serde_host_addr_human_unreadable_ $ty:snake>](node: HostAddr<$ty>) -> bool {
          let serialized = rmp_serde::to_vec(&node).unwrap();
          let deserialized: HostAddr<$ty> = rmp_serde::from_slice(&serialized).unwrap();
          node == deserialized
        }

        #[cfg(feature = "serde")]
        #[quickcheck_macros::quickcheck]
        fn [< fuzzy_serde_domain_human_readable_ $ty:snake>](node: Domain<$ty>) -> bool {
          let serialized = serde_json::to_string(&node).unwrap();
          let deserialized: Domain<$ty> = serde_json::from_str(&serialized).unwrap();
          node == deserialized
        }

        #[cfg(feature = "serde")]
        #[quickcheck_macros::quickcheck]
        fn [< fuzzy_serde_domain_human_unreadable_ $ty:snake>](node: Domain<$ty>) -> bool {
          let serialized = rmp_serde::to_vec(&node).unwrap();
          let deserialized: Domain<$ty> = rmp_serde::from_slice(&serialized).unwrap();
          node == deserialized
        }
      )*
    }
  };
}

gen_quickcheck!(String, RcStr, ArcStr, BoxStr, VecBytes, RcBytes, ArcBytes, BoxBytes,);

#[cfg(feature = "smol_str_0_3")]
gen_quickcheck!(SmolStr,);

#[cfg(feature = "bytes_1")]
gen_quickcheck!(Bytes,);
