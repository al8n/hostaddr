use quickcheck::{Arbitrary, Gen};

use super::{Domain, Host, HostAddr};

fn arbitrary_helper(g: &mut Gen) -> Domain<String> {
  let size = (usize::arbitrary(g) % 3) + 1; // 1-3 labels

  let mut domain = String::new();
  for i in 0..size {
    if i > 0 {
      domain.push('.');
    }

    let len = (usize::arbitrary(g) % 63) + 1;
    let chars: String = std::iter::from_fn(|| {
      let r = usize::arbitrary(g) % 64;
      Some(match r {
        0..=25 => (b'a' + (r as u8)) as char,
        26..=51 => (b'A' + (r as u8 - 26)) as char,
        52..=61 => (b'0' + (r as u8 - 52)) as char,
        62 => '_',
        _ => '-',
      })
    })
    .take(len)
    .collect();

    // Ensure valid first/last chars
    let mut label = chars;
    if label.starts_with('-') {
      label.replace_range(0..1, "a");
    }
    if label.ends_with('-') {
      label.replace_range(label.len() - 1..label.len(), "a");
    }

    domain.push_str(&label);
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

  // Maybe add trailing dot
  if bool::arbitrary(g) {
    domain.push('.');
  }

  Domain::try_from(domain).unwrap_or_else(|_| Domain::try_from("example.com").unwrap())
}

macro_rules! impl_arbitrary {
  ($($ty:ty { $expr:expr }), +$(,)?) => {
    $(
      impl Arbitrary for Domain<$ty> {
        fn arbitrary(g: &mut Gen) -> Self {
          $expr(arbitrary_helper(g))
        }
      }

      impl Arbitrary for Host<$ty> {
        fn arbitrary(g: &mut Gen) -> Self {
          if bool::arbitrary(g) {
            Host::Domain(Arbitrary::arbitrary(g))
          } else {
            Host::Ip(Arbitrary::arbitrary(g))
          }
        }
      }

      impl Arbitrary for HostAddr<$ty> {
        fn arbitrary(g: &mut Gen) -> Self {
          Self {
            host: Arbitrary::arbitrary(g),
            port: Arbitrary::arbitrary(g),
          }
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
);

#[cfg(feature = "smol_str_0_3")]
impl_arbitrary!(
  smol_str_0_3::SmolStr { |d: Domain<String>| { Domain(d.0.into()) } },
);

#[cfg(feature = "triomphe_0_1")]
const _: () = {
  use triomphe_0_1::Arc;

  impl_arbitrary!(
    Arc<str> { |d: Domain<String>| { Domain(d.0.into()) } },
    Arc<[u8]> { |d: Domain<String>| { Domain(d.0.into_bytes().into()) } },
  );
};
