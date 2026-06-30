use core::net::{IpAddr, SocketAddr};

#[cfg(feature = "std")]
use std::path::Path;

use crate::HostAddr;

/// Any address accepted by a runtime.
///
/// `Addr` separates Internet host addresses from IPC transports while keeping
/// storage generic for each address family.
///
/// Enum variants store their payloads by value, so DST storage is represented
/// through sized references such as `Addr<&str, &Path, &[u8]>`.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "snake_case"))]
pub enum Addr<H, P, A> {
  /// A DNS/IP host address.
  Host(HostAddr<H>),
  /// A non-IP IPC address.
  Ipc(IpcAddr<P, A>),
}

impl<H, P, A> From<HostAddr<H>> for Addr<H, P, A> {
  #[inline]
  fn from(value: HostAddr<H>) -> Self {
    Self::Host(value)
  }
}

impl<H, P, A> From<IpcAddr<P, A>> for Addr<H, P, A> {
  #[inline]
  fn from(value: IpcAddr<P, A>) -> Self {
    Self::Ipc(value)
  }
}

/// A non-IP communication address.
///
/// Path-backed transports use `P`, and byte-backed transports use `A`. The
/// type intentionally does not contain [`HostAddr`] or [`SocketAddr`].
///
/// Enum variants store their payloads by value, so DST storage is represented
/// through sized references such as `IpcAddr<&Path, &[u8]>`.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "snake_case"))]
pub enum IpcAddr<P, A> {
  /// A Unix-domain socket pathname.
  Unix(UnixAddr<P>),
  /// A Linux abstract socket name, without the leading NUL byte.
  Abstract(AbstractAddr<A>),
  /// A Windows named-pipe pathname.
  NamedPipe(NamedPipeAddr<P>),
  /// A VM socket address.
  #[cfg(feature = "vsock")]
  #[cfg_attr(docsrs, doc(cfg(feature = "vsock")))]
  Vsock(VsockAddr),
}

impl<P, A> From<UnixAddr<P>> for IpcAddr<P, A> {
  #[inline]
  fn from(value: UnixAddr<P>) -> Self {
    Self::Unix(value)
  }
}

impl<P, A> From<AbstractAddr<A>> for IpcAddr<P, A> {
  #[inline]
  fn from(value: AbstractAddr<A>) -> Self {
    Self::Abstract(value)
  }
}

impl<P, A> From<NamedPipeAddr<P>> for IpcAddr<P, A> {
  #[inline]
  fn from(value: NamedPipeAddr<P>) -> Self {
    Self::NamedPipe(value)
  }
}

#[cfg(feature = "vsock")]
#[cfg_attr(docsrs, doc(cfg(feature = "vsock")))]
impl<P, A> From<VsockAddr> for IpcAddr<P, A> {
  #[inline]
  fn from(value: VsockAddr) -> Self {
    Self::Vsock(value)
  }
}

/// A Unix-domain socket pathname.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
#[repr(transparent)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct UnixAddr<P: ?Sized>(P);

impl<P> UnixAddr<P> {
  /// Creates a Unix-domain socket address from path storage.
  #[inline]
  pub const fn new(path: P) -> Self {
    Self(path)
  }

  /// Returns the inner path storage by value.
  #[inline]
  pub fn into_inner(self) -> P {
    self.0
  }
}

impl<P: ?Sized> UnixAddr<P> {
  /// Converts a reference to path storage into a borrowed Unix-domain socket address.
  #[inline]
  pub const fn from_ref(path: &P) -> &Self {
    // SAFETY: UnixAddr<P> is #[repr(transparent)] over P, so references to P
    // and UnixAddr<P> have the same layout and metadata, including for DSTs.
    unsafe { &*(path as *const P as *const Self) }
  }

  /// Returns the inner path storage.
  #[inline]
  pub const fn as_inner(&self) -> &P {
    &self.0
  }

  /// Converts from `&UnixAddr<P>` to `UnixAddr<&P>`.
  #[inline]
  pub const fn as_ref(&self) -> UnixAddr<&P> {
    UnixAddr(&self.0)
  }

  /// Converts from `UnixAddr<P>` to `UnixAddr<&P::Target>`.
  #[inline]
  pub fn as_deref(&self) -> UnixAddr<&P::Target>
  where
    P: core::ops::Deref,
  {
    UnixAddr(core::ops::Deref::deref(&self.0))
  }
}

#[cfg(feature = "std")]
impl<P: ?Sized> UnixAddr<P>
where
  P: AsRef<Path>,
{
  /// Returns the address as a filesystem path.
  #[inline]
  pub fn as_path(&self) -> &Path {
    self.0.as_ref()
  }
}

#[cfg(feature = "std")]
impl UnixAddr<Path> {
  /// Converts a filesystem path reference into a borrowed Unix-domain socket address.
  #[inline]
  pub fn from_path(path: &Path) -> &Self {
    Self::from_ref(path)
  }
}

impl<P: ?Sized> core::borrow::Borrow<P> for UnixAddr<P> {
  #[inline]
  fn borrow(&self) -> &P {
    &self.0
  }
}

impl<P> From<P> for UnixAddr<P> {
  #[inline]
  fn from(value: P) -> Self {
    Self::new(value)
  }
}

/// A Windows named-pipe pathname.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
#[repr(transparent)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct NamedPipeAddr<P: ?Sized>(P);

impl<P> NamedPipeAddr<P> {
  /// Creates a Windows named-pipe address from path storage.
  #[inline]
  pub const fn new(path: P) -> Self {
    Self(path)
  }

  /// Returns the inner path storage by value.
  #[inline]
  pub fn into_inner(self) -> P {
    self.0
  }
}

impl<P: ?Sized> NamedPipeAddr<P> {
  /// Converts a reference to path storage into a borrowed named-pipe address.
  #[inline]
  pub const fn from_ref(path: &P) -> &Self {
    // SAFETY: NamedPipeAddr<P> is #[repr(transparent)] over P, so references to
    // P and NamedPipeAddr<P> have the same layout and metadata, including for DSTs.
    unsafe { &*(path as *const P as *const Self) }
  }

  /// Returns the inner path storage.
  #[inline]
  pub const fn as_inner(&self) -> &P {
    &self.0
  }

  /// Converts from `&NamedPipeAddr<P>` to `NamedPipeAddr<&P>`.
  #[inline]
  pub const fn as_ref(&self) -> NamedPipeAddr<&P> {
    NamedPipeAddr(&self.0)
  }

  /// Converts from `NamedPipeAddr<P>` to `NamedPipeAddr<&P::Target>`.
  #[inline]
  pub fn as_deref(&self) -> NamedPipeAddr<&P::Target>
  where
    P: core::ops::Deref,
  {
    NamedPipeAddr(core::ops::Deref::deref(&self.0))
  }
}

#[cfg(feature = "std")]
impl<P: ?Sized> NamedPipeAddr<P>
where
  P: AsRef<Path>,
{
  /// Returns the address as a filesystem path.
  #[inline]
  pub fn as_path(&self) -> &Path {
    self.0.as_ref()
  }
}

#[cfg(feature = "std")]
impl NamedPipeAddr<Path> {
  /// Converts a filesystem path reference into a borrowed named-pipe address.
  #[inline]
  pub fn from_path(path: &Path) -> &Self {
    Self::from_ref(path)
  }
}

impl<P: ?Sized> core::borrow::Borrow<P> for NamedPipeAddr<P> {
  #[inline]
  fn borrow(&self) -> &P {
    &self.0
  }
}

impl<P> From<P> for NamedPipeAddr<P> {
  #[inline]
  fn from(value: P) -> Self {
    Self::new(value)
  }
}

/// A Linux abstract socket name.
///
/// The stored bytes do not include the leading NUL byte used by the kernel.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
#[repr(transparent)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct AbstractAddr<A: ?Sized>(A);

impl<A> AbstractAddr<A> {
  /// Creates an abstract socket address from byte storage.
  #[inline]
  pub const fn new(name: A) -> Self {
    Self(name)
  }

  /// Returns the inner byte storage by value.
  #[inline]
  pub fn into_inner(self) -> A {
    self.0
  }
}

impl<A: ?Sized> AbstractAddr<A> {
  /// Converts a reference to byte storage into a borrowed abstract socket address.
  #[inline]
  pub const fn from_ref(name: &A) -> &Self {
    // SAFETY: AbstractAddr<A> is #[repr(transparent)] over A, so references to
    // A and AbstractAddr<A> have the same layout and metadata, including for DSTs.
    unsafe { &*(name as *const A as *const Self) }
  }

  /// Returns the inner byte storage.
  #[inline]
  pub const fn as_inner(&self) -> &A {
    &self.0
  }

  /// Converts from `&AbstractAddr<A>` to `AbstractAddr<&A>`.
  #[inline]
  pub const fn as_ref(&self) -> AbstractAddr<&A> {
    AbstractAddr(&self.0)
  }

  /// Converts from `AbstractAddr<A>` to `AbstractAddr<&A::Target>`.
  #[inline]
  pub fn as_deref(&self) -> AbstractAddr<&A::Target>
  where
    A: core::ops::Deref,
  {
    AbstractAddr(core::ops::Deref::deref(&self.0))
  }
}

impl<A: ?Sized> AbstractAddr<A>
where
  A: AsRef<[u8]>,
{
  /// Returns the abstract socket name bytes without a leading NUL byte.
  #[inline]
  pub fn as_bytes(&self) -> &[u8] {
    self.0.as_ref()
  }
}

impl AbstractAddr<[u8]> {
  /// Converts bytes into a borrowed abstract socket address.
  ///
  /// The input must not include the leading NUL byte used by the kernel.
  #[inline]
  pub const fn from_bytes(name: &[u8]) -> &Self {
    Self::from_ref(name)
  }
}

impl<A: ?Sized> core::borrow::Borrow<A> for AbstractAddr<A> {
  #[inline]
  fn borrow(&self) -> &A {
    &self.0
  }
}

impl<A> From<A> for AbstractAddr<A> {
  #[inline]
  fn from(value: A) -> Self {
    Self::new(value)
  }
}

/// A VM socket address.
#[cfg(feature = "vsock")]
#[cfg_attr(docsrs, doc(cfg(feature = "vsock")))]
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct VsockAddr {
  cid: u32,
  port: u32,
}

#[cfg(feature = "vsock")]
#[cfg_attr(docsrs, doc(cfg(feature = "vsock")))]
impl VsockAddr {
  /// Creates a VM socket address from a context identifier and port.
  #[inline]
  pub const fn new(cid: u32, port: u32) -> Self {
    Self { cid, port }
  }

  /// Returns the VM context identifier.
  #[inline]
  pub const fn cid(&self) -> u32 {
    self.cid
  }

  /// Returns the VM socket port.
  #[inline]
  pub const fn port(&self) -> u32 {
    self.port
  }
}

#[cfg(feature = "vsock")]
#[cfg_attr(docsrs, doc(cfg(feature = "vsock")))]
impl From<(u32, u32)> for VsockAddr {
  #[inline]
  fn from((cid, port): (u32, u32)) -> Self {
    Self::new(cid, port)
  }
}

/// An address in the local-address taxonomy.
///
/// [`LocalAddr::Loopback`] is validated to contain only loopback IP socket
/// addresses. [`LocalAddr::Ipc`] groups non-IP IPC transport addresses, but it
/// does not prove that every IPC endpoint target is same-machine or otherwise
/// safe to use as a trust boundary.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "snake_case"))]
pub enum LocalAddr<P, A> {
  /// A loopback IP socket address.
  Loopback(LoopbackAddr),
  /// A non-IP IPC address.
  Ipc(IpcAddr<P, A>),
}

impl<P, A> From<LoopbackAddr> for LocalAddr<P, A> {
  #[inline]
  fn from(value: LoopbackAddr) -> Self {
    Self::Loopback(value)
  }
}

impl<P, A> From<IpcAddr<P, A>> for LocalAddr<P, A> {
  #[inline]
  fn from(value: IpcAddr<P, A>) -> Self {
    Self::Ipc(value)
  }
}

/// A socket address whose IP address is loopback.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
#[repr(transparent)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct LoopbackAddr(SocketAddr);

#[cfg(feature = "serde")]
impl<'de> serde::Deserialize<'de> for LoopbackAddr {
  #[inline]
  fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
  where
    D: serde::Deserializer<'de>,
  {
    let addr = SocketAddr::deserialize(deserializer)?;
    Self::new(addr).map_err(serde::de::Error::custom)
  }
}

impl LoopbackAddr {
  /// Creates a loopback address after validating the IP component.
  #[inline]
  pub const fn new(addr: SocketAddr) -> Result<Self, ParseLoopbackAddrError> {
    if addr.ip().is_loopback() {
      Ok(Self(addr))
    } else {
      Err(ParseLoopbackAddrError(()))
    }
  }

  /// Returns the inner socket address.
  #[inline]
  pub const fn as_socket_addr(&self) -> SocketAddr {
    self.0
  }

  /// Returns the inner socket address by value.
  #[inline]
  pub const fn into_socket_addr(self) -> SocketAddr {
    self.0
  }

  /// Returns the loopback IP address.
  #[inline]
  pub const fn ip(&self) -> IpAddr {
    self.0.ip()
  }

  /// Returns the socket port.
  #[inline]
  pub const fn port(&self) -> u16 {
    self.0.port()
  }
}

impl core::fmt::Display for LoopbackAddr {
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    self.0.fmt(f)
  }
}

impl TryFrom<SocketAddr> for LoopbackAddr {
  type Error = ParseLoopbackAddrError;

  #[inline]
  fn try_from(value: SocketAddr) -> Result<Self, Self::Error> {
    Self::new(value)
  }
}

impl From<LoopbackAddr> for SocketAddr {
  #[inline]
  fn from(value: LoopbackAddr) -> Self {
    value.into_socket_addr()
  }
}

/// The provided socket address is not a loopback address.
#[derive(Clone, Copy, Debug, Eq, PartialEq, thiserror::Error)]
#[error("{}", self.as_str())]
pub struct ParseLoopbackAddrError(());

impl ParseLoopbackAddrError {
  /// Returns the error message.
  #[inline]
  pub const fn as_str(&self) -> &'static str {
    "not a loopback socket address"
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn loopback_addr_accepts_only_loopback_ips() {
    let ipv4 = "127.1.2.3:8080".parse::<SocketAddr>().unwrap();
    let loopback = LoopbackAddr::try_from(ipv4).unwrap();
    assert_eq!(loopback.ip(), ipv4.ip());
    assert_eq!(loopback.port(), 8080);

    let ipv6 = "[::1]:443".parse::<SocketAddr>().unwrap();
    assert_eq!(LoopbackAddr::new(ipv6).unwrap().as_socket_addr(), ipv6);

    let public = "192.0.2.1:8080".parse::<SocketAddr>().unwrap();
    assert_eq!(
      LoopbackAddr::try_from(public).unwrap_err().as_str(),
      "not a loopback socket address"
    );
  }

  #[test]
  fn ipc_addresses_preserve_storage() {
    let unix = UnixAddr::new("/tmp/app.sock");
    assert_eq!(unix.as_inner(), &"/tmp/app.sock");

    let abstract_addr = AbstractAddr::new(b"app.sock".as_slice());
    assert_eq!(abstract_addr.as_bytes(), b"app.sock");

    let pipe = NamedPipeAddr::new(r"\\.\pipe\app");
    assert_eq!(pipe.as_inner(), &r"\\.\pipe\app");

    #[cfg(feature = "vsock")]
    {
      let vsock = VsockAddr::new(3, 1024);
      assert_eq!(vsock.cid(), 3);
      assert_eq!(vsock.port(), 1024);
    }
  }

  #[test]
  fn ipc_wrappers_support_unsized_storage_refs() {
    let abstract_addr: &AbstractAddr<[u8]> = AbstractAddr::from_bytes(b"app.sock");
    assert_eq!(abstract_addr.as_bytes(), b"app.sock");
    assert_eq!(abstract_addr.as_ref().as_inner(), &b"app.sock".as_slice());

    #[cfg(feature = "std")]
    {
      let unix_path = std::path::Path::new("/tmp/app.sock");
      let unix: &UnixAddr<std::path::Path> = UnixAddr::from_path(unix_path);
      assert_eq!(unix.as_path(), unix_path);
      assert_eq!(unix.as_ref().as_inner(), &unix_path);

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

    let ipc: IpcAddr<&str, &[u8]> = UnixAddr::new("/tmp/app.sock").into();
    let addr: Addr<&str, &str, &[u8]> = ipc.into();
    assert!(matches!(addr, Addr::Ipc(IpcAddr::Unix(_))));

    let loopback = LoopbackAddr::try_from("127.0.0.1:8080".parse::<SocketAddr>().unwrap()).unwrap();
    let local: LocalAddr<&str, &[u8]> = loopback.into();
    assert!(matches!(local, LocalAddr::Loopback(_)));
  }

  #[cfg(feature = "serde")]
  #[test]
  fn serde_preserves_loopback_invariant() {
    let loopback = LoopbackAddr::try_from("127.0.0.1:8080".parse::<SocketAddr>().unwrap()).unwrap();
    let serialized = serde_json::to_string(&loopback).unwrap();
    let deserialized: LoopbackAddr = serde_json::from_str(&serialized).unwrap();
    assert_eq!(deserialized, loopback);

    assert!(serde_json::from_str::<LoopbackAddr>("\"192.0.2.1:8080\"").is_err());
  }
}
