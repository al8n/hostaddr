#[cfg(feature = "std")]
fn main() {
  use core::net::{IpAddr, SocketAddr};

  use hostaddr::{HostAddr, LoopbackAddr, PrivateIpAddr};

  let endpoint: HostAddr<String> = "example.com:443".parse().unwrap();
  assert!(endpoint.is_domain());
  assert_eq!(endpoint.port(), Some(443));

  let private = PrivateIpAddr::try_from("10.0.0.1".parse::<IpAddr>().unwrap()).unwrap();
  assert_eq!(private.to_string(), "10.0.0.1");

  let loopback = LoopbackAddr::try_from("127.0.0.1:8080".parse::<SocketAddr>().unwrap()).unwrap();
  assert_eq!(loopback.port(), 8080);
}

#[cfg(not(feature = "std"))]
fn main() {}
