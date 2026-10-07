#![cfg(feature = "serde")]

use core::{
  fmt::Debug,
  net::{IpAddr, SocketAddr, SocketAddrV6},
};

use hostaddr::{
  Addr, Buffer, Domain, Host, HostAddr, LinkLocalAddr, LocalAddr, LoopbackAddr, LoopbackIpAddr,
};
#[cfg(unix)]
use hostaddr::{IpcAddr, UnixAddr};
use serde::{de::DeserializeOwned, Serialize};

fn assert_wire<T>(value: &T, json: &str, bincode: &[u8])
where
  T: Serialize + DeserializeOwned + Debug + PartialEq,
{
  assert_eq!(serde_json::to_string(value).unwrap(), json);
  assert_eq!(serde_json::from_str::<T>(json).unwrap(), *value);
  assert_eq!(bincode::serialize(value).unwrap(), bincode);
  assert_eq!(bincode::deserialize::<T>(bincode).unwrap(), *value);
}

#[test]
fn rc1_domain_host_and_hostaddr_wire_is_frozen() {
  const DOMAIN: &[u8] = &[
    11, 0, 0, 0, 0, 0, 0, 0, 101, 120, 97, 109, 112, 108, 101, 46, 99, 111, 109,
  ];
  const HOST_DOMAIN: &[u8] = &[
    1, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 101, 120, 97, 109, 112, 108, 101, 46, 99, 111, 109,
  ];
  const HOST_IP: &[u8] = &[0, 0, 0, 0, 0, 0, 0, 0, 127, 0, 0, 1];
  const HOSTADDR_DOMAIN: &[u8] = &[
    1, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 101, 120, 97, 109, 112, 108, 101, 46, 99, 111, 109, 1,
    187, 1,
  ];
  const HOSTADDR_IP: &[u8] = &[0, 0, 0, 0, 0, 0, 0, 0, 127, 0, 0, 1, 1, 144, 31];

  let domain = Domain::<String>::try_from("example.com").unwrap();
  assert_wire(&domain, "\"example.com\"", DOMAIN);

  let buffer = Domain::<Buffer>::try_from("example.com")
    .unwrap()
    .into_inner();
  assert_wire(&buffer, "\"example.com\"", DOMAIN);

  let host = Host::<String>::try_from("example.com").unwrap();
  assert_wire(&host, r#"{"domain":"example.com"}"#, HOST_DOMAIN);

  let host = Host::<String>::from_ip("127.0.0.1".parse().unwrap());
  assert_wire(&host, r#"{"ip":"127.0.0.1"}"#, HOST_IP);

  let addr = HostAddr::<String>::try_from("example.com:443").unwrap();
  assert_wire(
    &addr,
    r#"{"host":{"domain":"example.com"},"port":443}"#,
    HOSTADDR_DOMAIN,
  );

  let addr = HostAddr::<String>::from(("127.0.0.1".parse::<IpAddr>().unwrap(), 8080));
  assert_wire(
    &addr,
    r#"{"host":{"ip":"127.0.0.1"},"port":8080}"#,
    HOSTADDR_IP,
  );
}

#[test]
fn semantic_ip_and_socket_wire_is_frozen_and_backward_compatible() {
  const LOOPBACK_IP: &[u8] = &[0, 0, 0, 0, 127, 0, 0, 1];
  const LOOPBACK_V4: &[u8] = &[0, 0, 0, 0, 127, 0, 0, 1, 144, 31];
  const LOOPBACK_V6: &[u8] = &[
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 187, 1,
  ];
  const LINK_LOCAL_V6_EXTENDED: &[u8] = &[
    2, 0, 0, 0, 254, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 187, 1, 7, 0, 0, 0, 42, 0, 0, 0,
  ];

  let ip = LoopbackIpAddr::try_from("127.0.0.1".parse::<IpAddr>().unwrap()).unwrap();
  assert_wire(&ip, "\"127.0.0.1\"", LOOPBACK_IP);

  let v4 = LoopbackAddr::try_from("127.0.0.1:8080".parse::<SocketAddr>().unwrap()).unwrap();
  assert_wire(&v4, r#"{"v4":{"ip":"127.0.0.1","port":8080}}"#, LOOPBACK_V4);
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
    LOOPBACK_V6,
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
  assert_wire(
    &scoped,
    r#"{"v6":{"ip":"fe80::1","port":443,"flowinfo":7,"scope_id":42}}"#,
    LINK_LOCAL_V6_EXTENDED,
  );

  for invalid in [
    &[0, 0, 0, 0, 192, 0, 2, 1, 80, 0][..],
    &[
      1, 0, 0, 0, 32, 1, 13, 184, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 80, 0,
    ][..],
    &[
      2, 0, 0, 0, 32, 1, 13, 184, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 80, 0, 7, 0, 0, 0, 42, 0, 0,
      0,
    ][..],
  ] {
    assert!(bincode::deserialize::<LoopbackAddr>(invalid).is_err());
  }
}

#[test]
fn aggregate_address_wire_is_literal_and_accepts_rc1_semantic_json() {
  const ADDR: &[u8] = &[
    0, 1, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 101, 120, 97, 109, 112, 108, 101, 46, 99, 111, 109, 1,
    187, 1,
  ];
  const LOCAL: &[u8] = &[0, 0, 0, 0, 0, 127, 0, 0, 1, 144, 31];

  let host = HostAddr::<String>::try_from("example.com:443").unwrap();
  let addr: Addr<String, String, Vec<u8>> = host.into();
  assert_wire(
    &addr,
    r#"{"host":{"host":{"domain":"example.com"},"port":443}}"#,
    ADDR,
  );

  let loopback = LoopbackAddr::try_from("127.0.0.1:8080".parse::<SocketAddr>().unwrap()).unwrap();
  let local: LocalAddr<String, Vec<u8>> = loopback.into();
  assert_wire(
    &local,
    r#"{"loopback":{"v4":{"ip":"127.0.0.1","port":8080}}}"#,
    LOCAL,
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
  const IPC: &[u8] = &[
    0, 13, 0, 0, 0, 0, 0, 0, 0, 47, 116, 109, 112, 47, 97, 112, 112, 46, 115, 111, 99, 107,
  ];

  let ipc: IpcAddr<String, Vec<u8>> = UnixAddr::new(String::from("/tmp/app.sock")).into();
  assert_wire(&ipc, r#"["unix","/tmp/app.sock"]"#, IPC);
}
