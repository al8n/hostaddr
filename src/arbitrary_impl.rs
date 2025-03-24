use arbitrary::{Arbitrary, Result, Unstructured};

use super::{Domain, Host, HostAddr};

fn arbitrary_helper(u: &mut Unstructured<'_>) -> Result<Domain<String>> {
  // Generate between 1 and 4 labels
  let label_count = u.int_in_range(1..=4)?;
  let mut domain = String::new();

  for i in 0..label_count {
    if i > 0 {
      domain.push('.');
    }

    // Generate label length (1-63)
    let len = u.int_in_range(1..=63)?;

    // First character can't be hyphen but can be underscore
    let first_char = if u.arbitrary::<bool>()? {
      // letter
      let c = u.int_in_range(0..=51)?;
      if c < 26 {
        b'a' + c
      } else {
        b'A' + (c - 26)
      }
    } else if u.arbitrary::<bool>()? {
      // number
      u.int_in_range(b'0'..=b'9')?
    } else {
      b'_'
    } as char;

    domain.push(first_char);

    // Rest of the characters
    for _ in 1..len {
      let c = match u.int_in_range(0..=4)? {
        0 => u.int_in_range(b'a'..=b'z')? as char,
        1 => u.int_in_range(b'A'..=b'Z')? as char,
        2 => u.int_in_range(b'0'..=b'9')? as char,
        3 => '_',
        _ => {
          if len > 1 {
            '-'
          } else {
            u.int_in_range(b'a'..=b'z')? as char
          }
        }
      };
      domain.push(c);
    }

    // Ensure last char isn't hyphen
    if domain.ends_with('-') {
      domain.push('a');
    }
  }

  // Ensure last label isn't numeric-only
  if domain
    .split('.')
    .next_back()
    .unwrap()
    .chars()
    .all(|c| c.is_ascii_digit())
  {
    domain.push('x');
  }

  // Optionally add trailing dot
  if u.arbitrary::<bool>()? {
    domain.push('.');
  }

  Domain::<String>::try_from(domain).map_err(|_| arbitrary::Error::IncorrectFormat)
}

macro_rules! impl_arbitrary {
  ($($ty:ty { $expr:expr }), +$(,)?) => {
    $(
      impl<'a> Arbitrary<'a> for Domain<$ty> {
        fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
          arbitrary_helper(u).map(|d| $expr(d))
        }
      }

      impl<'a> Arbitrary<'a> for Host<$ty> {
        fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
          Ok(if u.arbitrary()? {
            Host::Domain(<Domain<$ty> as Arbitrary>::arbitrary(u)?.0)
          } else {
            Host::Ip(Arbitrary::arbitrary(u)?)
          })
        }
      }

      impl<'a> Arbitrary<'a> for HostAddr<$ty> {
        fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
          Ok(Self {
            host: Arbitrary::arbitrary(u)?,
            port: u.arbitrary()?,
          })
        }
      }
    )*
  };
}

impl_arbitrary!(
  String { |d| { d } },
  std::sync::Arc<str> { |d: Domain<String>| { Domain(d.0.into()) } },
  std::boxed::Box<str> { |d: Domain<String>| { Domain(d.0.into_boxed_str()) } },
  std::rc::Rc<str> { |d: Domain<String>| { Domain(d.0.into()) } },
  Vec<u8> { |d: Domain<String>| { Domain(d.0.into_bytes()) } },
  std::sync::Arc<[u8]> { |d: Domain<String>| { Domain(d.0.into_bytes().into()) } },
  std::boxed::Box<[u8]> { |d: Domain<String>| { Domain(d.0.into_bytes().into_boxed_slice()) } },
  std::rc::Rc<[u8]> { |d: Domain<String>| { Domain(d.0.into_bytes().into()) } },
  std::borrow::Cow<'a, str> { |d: Domain<String>| { Domain(d.0.into()) } },
);

#[cfg(feature = "smol_str_0_3")]
impl_arbitrary!(
  smol_str_0_3::SmolStr { |d: Domain<String>| { Domain(d.0.into()) } },
);

#[cfg(feature = "bytes_1")]
impl_arbitrary!(
  bytes_1::Bytes { |d: Domain<String>| { Domain(d.0.into_bytes().into()) } },
);

#[cfg(feature = "triomphe_0_1")]
const _: () = {
  use triomphe_0_1::Arc;

  impl_arbitrary!(
    Arc<str> { |d: Domain<String>| { Domain(d.0.into()) } },
    Arc<[u8]> { |d: Domain<String>| { Domain(d.0.into_bytes().into()) } },
  );
};
