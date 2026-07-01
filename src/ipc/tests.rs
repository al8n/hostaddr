use super::*;
use core::net::{IpAddr, SocketAddr};

#[cfg(all(feature = "serde", any(all(unix, not(target_os = "linux")), windows)))]
struct NonSerde;

#[cfg(feature = "serde")]
fn assert_bincode_ipc_roundtrip(ipc: IpcAddr<&str, &[u8]>) {
  let serialized = bincode::serialize(&ipc).unwrap();
  let deserialized: IpcAddr<&str, &[u8]> = bincode::deserialize(&serialized).unwrap();
  assert_eq!(deserialized, ipc);

  let addr: Addr<&str, &str, &[u8]> = ipc.into();
  let serialized = bincode::serialize(&addr).unwrap();
  let deserialized: Addr<&str, &str, &[u8]> = bincode::deserialize(&serialized).unwrap();
  assert_eq!(deserialized, addr);

  let local: LocalAddr<&str, &[u8]> = ipc.into();
  let serialized = bincode::serialize(&local).unwrap();
  let deserialized: LocalAddr<&str, &[u8]> = bincode::deserialize(&serialized).unwrap();
  assert_eq!(deserialized, local);
}

#[test]
fn ipc_addresses_preserve_storage() {
  #[cfg(unix)]
  {
    let unix = UnixAddr::new("/tmp/app.sock");
    assert_eq!(unix.as_inner(), &"/tmp/app.sock");
  }

  #[cfg(target_os = "linux")]
  {
    let abstract_addr = AbstractAddr::new(b"app.sock".as_slice());
    assert_eq!(abstract_addr.as_bytes(), b"app.sock");
  }

  #[cfg(windows)]
  {
    let pipe = NamedPipeAddr::new(r"\\.\pipe\app");
    assert_eq!(pipe.as_inner(), &r"\\.\pipe\app");
  }

  #[cfg(all(feature = "vsock", target_os = "linux"))]
  {
    let vsock = VsockAddr::new(3, 1024);
    assert_eq!(vsock.cid(), 3);
    assert_eq!(vsock.port(), 1024);
  }
}

#[test]
fn ipc_wrappers_support_unsized_storage_refs() {
  #[cfg(target_os = "linux")]
  {
    let abstract_addr: &AbstractAddr<[u8]> = AbstractAddr::from_bytes(b"app.sock");
    assert_eq!(abstract_addr.as_bytes(), b"app.sock");
    assert_eq!(abstract_addr.as_ref().as_inner(), &b"app.sock".as_slice());
  }

  #[cfg(all(feature = "std", unix))]
  {
    let unix_path = std::path::Path::new("/tmp/app.sock");
    let unix: &UnixAddr<std::path::Path> = UnixAddr::from_path(unix_path);
    assert_eq!(unix.as_path(), unix_path);
    assert_eq!(unix.as_ref().as_inner(), &unix_path);
  }

  #[cfg(all(feature = "std", windows))]
  {
    let pipe_path = std::path::Path::new(r"\\.\pipe\app");
    let pipe: &NamedPipeAddr<std::path::Path> = NamedPipeAddr::from_path(pipe_path);
    assert_eq!(pipe.as_path(), pipe_path);
    assert_eq!(pipe.as_ref().as_inner(), &pipe_path);
  }
}

#[test]
fn address_conversions_follow_taxonomy() {
  let host = HostAddr::<&str>::from(("127.0.0.1".parse::<IpAddr>().unwrap(), 8080));
  let addr: Addr<&str, &str, &[u8]> = host.into();
  assert!(matches!(addr, Addr::Host(_)));

  #[cfg(unix)]
  {
    let ipc: IpcAddr<&str, &[u8]> = UnixAddr::new("/tmp/app.sock").into();
    let addr: Addr<&str, &str, &[u8]> = ipc.into();
    assert!(matches!(addr, Addr::Ipc(IpcAddr::Unix(_))));
  }

  #[cfg(windows)]
  {
    let ipc: IpcAddr<&str, &[u8]> = NamedPipeAddr::new(r"\\.\pipe\app").into();
    let addr: Addr<&str, &str, &[u8]> = ipc.into();
    assert!(matches!(addr, Addr::Ipc(IpcAddr::NamedPipe(_))));
  }

  let loopback = LoopbackAddr::try_from("127.0.0.1:8080".parse::<SocketAddr>().unwrap()).unwrap();
  let local: LocalAddr<&str, &[u8]> = loopback.into();
  assert!(matches!(local, LocalAddr::Loopback(_)));
}

#[cfg(feature = "serde")]
#[test]
fn serde_visitors_accept_supported_tag_forms() {
  use serde::de::Visitor as _;

  type Error = serde::de::value::Error;

  assert!(matches!(
    AddrVariantVisitor.visit_str::<Error>("host").unwrap(),
    AddrVariant::Host
  ));
  assert!(matches!(
    AddrVariantVisitor.visit_str::<Error>("ipc").unwrap(),
    AddrVariant::Ipc
  ));
  assert!(AddrVariantVisitor.visit_str::<Error>("other").is_err());
  assert!(matches!(
    AddrVariantVisitor.visit_bytes::<Error>(b"host").unwrap(),
    AddrVariant::Host
  ));
  assert!(matches!(
    AddrVariantVisitor.visit_bytes::<Error>(b"ipc").unwrap(),
    AddrVariant::Ipc
  ));
  assert!(AddrVariantVisitor.visit_bytes::<Error>(b"other").is_err());
  assert!(AddrVariantVisitor.visit_bytes::<Error>(b"\xff").is_err());
  assert!(matches!(
    AddrVariantVisitor.visit_u8::<Error>(0).unwrap(),
    AddrVariant::Host
  ));
  assert!(matches!(
    AddrVariantVisitor.visit_u16::<Error>(1).unwrap(),
    AddrVariant::Ipc
  ));
  assert!(matches!(
    AddrVariantVisitor.visit_u32::<Error>(0).unwrap(),
    AddrVariant::Host
  ));
  assert!(AddrVariantVisitor.visit_u64::<Error>(2).is_err());

  assert!(matches!(
    IpcAddrTagVisitor.visit_str::<Error>("unix").unwrap(),
    IpcAddrTag::Unix
  ));
  assert!(matches!(
    IpcAddrTagVisitor.visit_str::<Error>("abstract").unwrap(),
    IpcAddrTag::Abstract
  ));
  assert!(matches!(
    IpcAddrTagVisitor.visit_str::<Error>("named_pipe").unwrap(),
    IpcAddrTag::NamedPipe
  ));
  assert!(matches!(
    IpcAddrTagVisitor.visit_str::<Error>("vsock").unwrap(),
    IpcAddrTag::Vsock
  ));
  assert!(IpcAddrTagVisitor.visit_str::<Error>("other").is_err());
  assert!(matches!(
    IpcAddrTagVisitor.visit_bytes::<Error>(b"unix").unwrap(),
    IpcAddrTag::Unix
  ));
  assert!(matches!(
    IpcAddrTagVisitor.visit_bytes::<Error>(b"abstract").unwrap(),
    IpcAddrTag::Abstract
  ));
  assert!(matches!(
    IpcAddrTagVisitor
      .visit_bytes::<Error>(b"named_pipe")
      .unwrap(),
    IpcAddrTag::NamedPipe
  ));
  assert!(matches!(
    IpcAddrTagVisitor.visit_bytes::<Error>(b"vsock").unwrap(),
    IpcAddrTag::Vsock
  ));
  assert!(IpcAddrTagVisitor.visit_bytes::<Error>(b"other").is_err());

  assert!(matches!(
    LocalAddrVariantVisitor
      .visit_str::<Error>("loopback")
      .unwrap(),
    LocalAddrVariant::Loopback
  ));
  assert!(matches!(
    LocalAddrVariantVisitor.visit_str::<Error>("ipc").unwrap(),
    LocalAddrVariant::Ipc
  ));
  assert!(LocalAddrVariantVisitor.visit_str::<Error>("other").is_err());
  assert!(matches!(
    LocalAddrVariantVisitor
      .visit_bytes::<Error>(b"loopback")
      .unwrap(),
    LocalAddrVariant::Loopback
  ));
  assert!(matches!(
    LocalAddrVariantVisitor
      .visit_bytes::<Error>(b"ipc")
      .unwrap(),
    LocalAddrVariant::Ipc
  ));
  assert!(LocalAddrVariantVisitor
    .visit_bytes::<Error>(b"other")
    .is_err());
  assert!(LocalAddrVariantVisitor
    .visit_bytes::<Error>(b"\xff")
    .is_err());
  assert!(matches!(
    LocalAddrVariantVisitor.visit_u8::<Error>(0).unwrap(),
    LocalAddrVariant::Loopback
  ));
  assert!(matches!(
    LocalAddrVariantVisitor.visit_u16::<Error>(1).unwrap(),
    LocalAddrVariant::Ipc
  ));
  assert!(matches!(
    LocalAddrVariantVisitor.visit_u32::<Error>(0).unwrap(),
    LocalAddrVariant::Loopback
  ));
  assert!(LocalAddrVariantVisitor.visit_u64::<Error>(2).is_err());

  let _ = <Error as serde::de::Error>::invalid_type(
    serde::de::Unexpected::Unit,
    &AddrVisitor::<&str, &str, &[u8]>::new(),
  );
  let _ = <Error as serde::de::Error>::invalid_length(0, &IpcAddrVisitor::<&str, &[u8]>::new());
  let _ = <Error as serde::de::Error>::invalid_type(
    serde::de::Unexpected::Unit,
    &LocalAddrVisitor::<&str, &[u8]>::new(),
  );
}

#[cfg(feature = "serde")]
#[test]
fn serde_roundtrips_host_and_loopback_wrappers() {
  let host = HostAddr::<&str>::from(("127.0.0.1".parse::<IpAddr>().unwrap(), 8080));
  let addr: Addr<&str, &str, &[u8]> = host.into();
  let serialized = serde_json::to_string(&addr).unwrap();
  assert!(serialized.contains("\"host\""));
  let deserialized: Addr<&str, &str, &[u8]> = serde_json::from_str(&serialized).unwrap();
  assert_eq!(deserialized, addr);

  let loopback = LoopbackAddr::try_from("127.0.0.1:8080".parse::<SocketAddr>().unwrap()).unwrap();
  let local: LocalAddr<&str, &[u8]> = loopback.into();
  let serialized = serde_json::to_string(&local).unwrap();
  assert!(serialized.contains("\"loopback\""));
  let deserialized: LocalAddr<&str, &[u8]> = serde_json::from_str(&serialized).unwrap();
  assert_eq!(deserialized, local);
}

#[cfg(all(unix, any(feature = "std", feature = "alloc")))]
#[test]
fn unix_addr_conversion_helpers_preserve_inner_path() {
  let unix = UnixAddr::new(crate::std::string::String::from("/tmp/app.sock"));
  assert_eq!(unix.as_deref().as_inner(), &"/tmp/app.sock");
  assert_eq!(unix.into_inner(), "/tmp/app.sock");

  let unix: UnixAddr<&str> = UnixAddr::from("/tmp/app.sock");
  assert_eq!(
    *core::borrow::Borrow::<&str>::borrow(&unix),
    "/tmp/app.sock"
  );
}

#[cfg(feature = "serde")]
#[test]
fn ipc_serde_uses_stable_tags() {
  #[cfg(unix)]
  {
    let ipc: IpcAddr<&str, &[u8]> = UnixAddr::new("/tmp/app.sock").into();
    let serialized = serde_json::to_string(&ipc).unwrap();
    assert!(serialized.contains("\"unix\""));
    let deserialized: IpcAddr<&str, &[u8]> = serde_json::from_str(&serialized).unwrap();
    assert_eq!(deserialized, ipc);

    let serialized = rmp_serde::to_vec(&ipc).unwrap();
    let deserialized: IpcAddr<&str, &[u8]> = rmp_serde::from_slice(&serialized).unwrap();
    assert_eq!(deserialized, ipc);

    assert_bincode_ipc_roundtrip(ipc);
  }

  #[cfg(target_os = "linux")]
  {
    let ipc: IpcAddr<&str, [u8; 8]> = AbstractAddr::new(*b"app.sock").into();
    let serialized = rmp_serde::to_vec(&ipc).unwrap();
    let deserialized: IpcAddr<&str, [u8; 8]> = rmp_serde::from_slice(&serialized).unwrap();
    assert_eq!(deserialized, ipc);

    let serialized = bincode::serialize(&ipc).unwrap();
    let deserialized: IpcAddr<&str, [u8; 8]> = bincode::deserialize(&serialized).unwrap();
    assert_eq!(deserialized, ipc);

    let addr: Addr<&str, &str, [u8; 8]> = ipc.into();
    let serialized = bincode::serialize(&addr).unwrap();
    let deserialized: Addr<&str, &str, [u8; 8]> = bincode::deserialize(&serialized).unwrap();
    assert_eq!(deserialized, addr);

    let local: LocalAddr<&str, [u8; 8]> = ipc.into();
    let serialized = bincode::serialize(&local).unwrap();
    let deserialized: LocalAddr<&str, [u8; 8]> = bincode::deserialize(&serialized).unwrap();
    assert_eq!(deserialized, local);
  }

  #[cfg(windows)]
  {
    let borrowed: IpcAddr<&str, &[u8]> = NamedPipeAddr::new(r"\\.\pipe\app").into();
    let serialized = serde_json::to_string(&borrowed).unwrap();
    assert!(serialized.contains("\"named_pipe\""));

    #[cfg(any(feature = "std", feature = "alloc"))]
    {
      use std::string::String;

      let ipc: IpcAddr<String, &[u8]> = NamedPipeAddr::new(String::from(r"\\.\pipe\app")).into();
      let serialized = serde_json::to_string(&ipc).unwrap();
      let deserialized: IpcAddr<String, &[u8]> = serde_json::from_str(&serialized).unwrap();
      assert_eq!(deserialized, ipc);
    }

    assert_bincode_ipc_roundtrip(borrowed);
  }

  #[cfg(all(feature = "vsock", target_os = "linux"))]
  {
    let ipc: IpcAddr<&str, &[u8]> = VsockAddr::new(3, 1024).into();
    let serialized = serde_json::to_string(&ipc).unwrap();
    assert!(serialized.contains("\"vsock\""));
    let deserialized: IpcAddr<&str, &[u8]> = serde_json::from_str(&serialized).unwrap();
    assert_eq!(deserialized, ipc);

    assert_bincode_ipc_roundtrip(ipc);
  }
}

#[cfg(all(feature = "serde", unix))]
#[test]
fn ipc_serde_uses_numeric_tags_for_binary_formats() {
  let ipc: IpcAddr<&str, &[u8]> = UnixAddr::new("/tmp/app.sock").into();
  let serialized = bincode::serialize(&ipc).unwrap();
  assert_eq!(serialized.first().copied(), Some(0));
  let deserialized: IpcAddr<&str, &[u8]> = bincode::deserialize(&serialized).unwrap();
  assert_eq!(deserialized, ipc);

  let addr: Addr<&str, &str, &[u8]> = ipc.into();
  let serialized = bincode::serialize(&addr).unwrap();
  assert_eq!(serialized.first().copied(), Some(1));
  assert_eq!(serialized.get(1).copied(), Some(0));
  let deserialized: Addr<&str, &str, &[u8]> = bincode::deserialize(&serialized).unwrap();
  assert_eq!(deserialized, addr);

  let local: LocalAddr<&str, &[u8]> = ipc.into();
  let serialized = bincode::serialize(&local).unwrap();
  assert_eq!(serialized.first().copied(), Some(1));
  assert_eq!(serialized.get(1).copied(), Some(0));
  let deserialized: LocalAddr<&str, &[u8]> = bincode::deserialize(&serialized).unwrap();
  assert_eq!(deserialized, local);
}

#[cfg(all(feature = "serde", not(windows)))]
#[test]
fn ipc_serde_rejects_unsupported_tags() {
  assert!(serde_json::from_str::<IpcAddr<&str, &[u8]>>("[\"named_pipe\",\"pipe\"]").is_err());

  #[cfg(not(all(feature = "vsock", target_os = "linux")))]
  assert!(serde_json::from_str::<IpcAddr<&str, &[u8]>>("[\"vsock\",null]").is_err());
}

#[cfg(all(feature = "serde", unix, not(target_os = "linux")))]
#[test]
fn ipc_serde_does_not_bound_unavailable_abstract_payload() {
  let ipc: IpcAddr<&str, NonSerde> = UnixAddr::new("/tmp/app.sock").into();
  let serialized = serde_json::to_string(&ipc).unwrap();
  let deserialized: IpcAddr<&str, NonSerde> = serde_json::from_str(&serialized).unwrap();
  assert!(matches!(deserialized, IpcAddr::Unix(_)));

  let addr: Addr<&str, &str, NonSerde> = IpcAddr::from(UnixAddr::new("/tmp/app.sock")).into();
  let serialized = serde_json::to_string(&addr).unwrap();
  let deserialized: Addr<&str, &str, NonSerde> = serde_json::from_str(&serialized).unwrap();
  assert!(matches!(deserialized, Addr::Ipc(IpcAddr::Unix(_))));

  let local: LocalAddr<&str, NonSerde> = IpcAddr::from(UnixAddr::new("/tmp/app.sock")).into();
  let serialized = serde_json::to_string(&local).unwrap();
  let deserialized: LocalAddr<&str, NonSerde> = serde_json::from_str(&serialized).unwrap();
  assert!(matches!(deserialized, LocalAddr::Ipc(IpcAddr::Unix(_))));
}

#[cfg(all(feature = "serde", windows))]
#[test]
fn ipc_serde_does_not_bound_unavailable_abstract_payload() {
  let borrowed: IpcAddr<&str, NonSerde> = NamedPipeAddr::new(r"\\.\pipe\app").into();
  let serialized = serde_json::to_string(&borrowed).unwrap();
  assert!(serialized.contains("\"named_pipe\""));

  #[cfg(any(feature = "std", feature = "alloc"))]
  {
    use std::string::String;

    let ipc: IpcAddr<String, NonSerde> = NamedPipeAddr::new(String::from(r"\\.\pipe\app")).into();
    let serialized = serde_json::to_string(&ipc).unwrap();
    let deserialized: IpcAddr<String, NonSerde> = serde_json::from_str(&serialized).unwrap();
    assert!(matches!(deserialized, IpcAddr::NamedPipe(_)));

    let addr: Addr<&str, String, NonSerde> =
      IpcAddr::from(NamedPipeAddr::new(String::from(r"\\.\pipe\app"))).into();
    let serialized = serde_json::to_string(&addr).unwrap();
    let deserialized: Addr<&str, String, NonSerde> = serde_json::from_str(&serialized).unwrap();
    assert!(matches!(deserialized, Addr::Ipc(IpcAddr::NamedPipe(_))));

    let local: LocalAddr<String, NonSerde> =
      IpcAddr::from(NamedPipeAddr::new(String::from(r"\\.\pipe\app"))).into();
    let serialized = serde_json::to_string(&local).unwrap();
    let deserialized: LocalAddr<String, NonSerde> = serde_json::from_str(&serialized).unwrap();
    assert!(matches!(
      deserialized,
      LocalAddr::Ipc(IpcAddr::NamedPipe(_))
    ));
  }
}
