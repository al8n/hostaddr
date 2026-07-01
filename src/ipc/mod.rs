#[cfg(all(feature = "std", any(unix, windows)))]
use std::path::Path;

use crate::{HostAddr, LoopbackAddr};
use core::marker::PhantomData;

#[cfg(test)]
mod tests;

/// Any address accepted by a runtime.
///
/// `Addr` separates Internet host addresses from IPC transports while keeping
/// storage generic for each address family.
///
/// Enum variants store their payloads by value, so DST storage is represented
/// through sized references such as `Addr<&str, &Path, &[u8]>`.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
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
/// type intentionally does not contain [`HostAddr`] or [`core::net::SocketAddr`].
///
/// Enum variants store their payloads by value, so DST storage is represented
/// through sized references such as `IpcAddr<&Path, &[u8]>`.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
#[non_exhaustive]
pub enum IpcAddr<P, A> {
  /// A Unix-domain socket pathname.
  #[cfg(unix)]
  #[cfg_attr(docsrs, doc(cfg(unix)))]
  Unix(UnixAddr<P>),
  /// A Linux abstract socket name, without the leading NUL byte.
  #[cfg(target_os = "linux")]
  #[cfg_attr(docsrs, doc(cfg(target_os = "linux")))]
  Abstract(AbstractAddr<A>),
  /// A Windows named-pipe pathname.
  #[cfg(windows)]
  #[cfg_attr(docsrs, doc(cfg(windows)))]
  NamedPipe(NamedPipeAddr<P>),
  /// A VM socket address.
  #[cfg(all(feature = "vsock", target_os = "linux"))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "vsock", target_os = "linux"))))]
  Vsock(VsockAddr),
  #[doc(hidden)]
  #[cfg(any(not(any(unix, windows)), not(target_os = "linux")))]
  __NonExhaustive(core::convert::Infallible, PhantomData<fn() -> (P, A)>),
}

#[cfg(unix)]
#[cfg_attr(docsrs, doc(cfg(unix)))]
impl<P, A> From<UnixAddr<P>> for IpcAddr<P, A> {
  #[inline]
  fn from(value: UnixAddr<P>) -> Self {
    Self::Unix(value)
  }
}

/// A Unix-domain socket pathname.
#[cfg(unix)]
#[cfg_attr(docsrs, doc(cfg(unix)))]
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
#[repr(transparent)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct UnixAddr<P: ?Sized>(P);

#[cfg(unix)]
#[cfg_attr(docsrs, doc(cfg(unix)))]
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

#[cfg(unix)]
#[cfg_attr(docsrs, doc(cfg(unix)))]
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

#[cfg(all(feature = "std", unix))]
#[cfg_attr(docsrs, doc(cfg(all(feature = "std", unix))))]
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

#[cfg(all(feature = "std", unix))]
#[cfg_attr(docsrs, doc(cfg(all(feature = "std", unix))))]
impl UnixAddr<Path> {
  /// Converts a filesystem path reference into a borrowed Unix-domain socket address.
  #[inline]
  pub fn from_path(path: &Path) -> &Self {
    Self::from_ref(path)
  }
}

#[cfg(unix)]
#[cfg_attr(docsrs, doc(cfg(unix)))]
impl<P: ?Sized> core::borrow::Borrow<P> for UnixAddr<P> {
  #[inline]
  fn borrow(&self) -> &P {
    &self.0
  }
}

#[cfg(unix)]
#[cfg_attr(docsrs, doc(cfg(unix)))]
impl<P> From<P> for UnixAddr<P> {
  #[inline]
  fn from(value: P) -> Self {
    Self::new(value)
  }
}

/// A Windows named-pipe pathname.
#[cfg(windows)]
#[cfg_attr(docsrs, doc(cfg(windows)))]
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
#[repr(transparent)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct NamedPipeAddr<P: ?Sized>(P);

/// A Linux abstract socket name.
///
/// The stored bytes do not include the leading NUL byte used by the kernel.
#[cfg(target_os = "linux")]
#[cfg_attr(docsrs, doc(cfg(target_os = "linux")))]
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
#[repr(transparent)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct AbstractAddr<A: ?Sized>(A);

/// A VM socket address.
#[cfg(all(feature = "vsock", target_os = "linux"))]
#[cfg_attr(docsrs, doc(cfg(all(feature = "vsock", target_os = "linux"))))]
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct VsockAddr {
  cid: u32,
  port: u32,
}

/// An address in the local-address taxonomy.
///
/// [`LocalAddr::Loopback`] is validated to contain only loopback IP socket
/// addresses. [`LocalAddr::Ipc`] groups non-IP IPC transport addresses, but it
/// does not prove that every IPC endpoint target is same-machine or otherwise
/// safe to use as a trust boundary.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
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

#[cfg(windows)]
#[cfg_attr(docsrs, doc(cfg(windows)))]
const _: () = {
  impl<P, A> From<NamedPipeAddr<P>> for IpcAddr<P, A> {
    #[inline]
    fn from(value: NamedPipeAddr<P>) -> Self {
      Self::NamedPipe(value)
    }
  }

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
  #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
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
  #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
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
};

#[cfg(target_os = "linux")]
#[cfg_attr(docsrs, doc(cfg(target_os = "linux")))]
const _: () = {
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

  impl<P, A> From<AbstractAddr<A>> for IpcAddr<P, A> {
    #[inline]
    fn from(value: AbstractAddr<A>) -> Self {
      Self::Abstract(value)
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
};

#[cfg(feature = "serde")]
struct IpcAddrTagVisitor;

#[cfg(feature = "serde")]
type AddrVisitorMarker<H, P, A> = PhantomData<fn() -> (H, P, A)>;

#[cfg(feature = "serde")]
struct IpcAddrVisitor<P, A> {
  marker: PhantomData<fn() -> (P, A)>,
}

#[cfg(feature = "serde")]
struct AddrVisitor<H, P, A> {
  marker: AddrVisitorMarker<H, P, A>,
}

#[cfg(feature = "serde")]
struct AddrVariantVisitor;

#[cfg(feature = "serde")]
struct LocalAddrVisitor<P, A> {
  marker: PhantomData<fn() -> (P, A)>,
}

#[cfg(feature = "serde")]
struct LocalAddrVariantVisitor;

#[cfg(feature = "serde")]
#[derive(Clone, Copy)]
enum LocalAddrVariant {
  Loopback,
  Ipc,
}

#[cfg(feature = "serde")]
#[derive(Clone, Copy)]
enum AddrVariant {
  Host,
  Ipc,
}

#[cfg(feature = "serde")]
#[derive(Clone, Copy)]
enum IpcAddrTag {
  Unix,
  Abstract,
  NamedPipe,
  Vsock,
}

#[cfg(feature = "serde")]
#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
const _: () = {
  use core::marker::PhantomData;
  use serde::{
    de::{self, EnumAccess, VariantAccess as _, Visitor},
    ser::SerializeTuple,
    Deserialize, Deserializer, Serialize, Serializer,
  };

  const IPC_ADDR_VARIANTS: &[&str] = &["unix", "abstract", "named_pipe", "vsock"];

  impl IpcAddrTag {
    #[inline]
    const fn as_str(self) -> &'static str {
      match self {
        Self::Unix => "unix",
        Self::Abstract => "abstract",
        Self::NamedPipe => "named_pipe",
        Self::Vsock => "vsock",
      }
    }

    #[inline]
    const fn as_u8(self) -> u8 {
      match self {
        Self::Unix => 0,
        Self::Abstract => 1,
        Self::NamedPipe => 2,
        Self::Vsock => 3,
      }
    }
  }

  impl Serialize for IpcAddrTag {
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
      S: Serializer,
    {
      if serializer.is_human_readable() {
        serializer.serialize_str((*self).as_str())
      } else {
        serializer.serialize_u8((*self).as_u8())
      }
    }
  }

  impl<'de> Deserialize<'de> for IpcAddrTag {
    #[inline]
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
      D: Deserializer<'de>,
    {
      if deserializer.is_human_readable() {
        deserializer.deserialize_str(IpcAddrTagVisitor)
      } else {
        deserializer.deserialize_u8(IpcAddrTagVisitor)
      }
    }
  }

  impl Visitor<'_> for IpcAddrTagVisitor {
    type Value = IpcAddrTag;

    #[inline]
    fn expecting(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
      formatter.write_str("an IPC address kind")
    }

    #[inline]
    fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
    where
      E: de::Error,
    {
      match value {
        "unix" => Ok(IpcAddrTag::Unix),
        "abstract" => Ok(IpcAddrTag::Abstract),
        "named_pipe" => Ok(IpcAddrTag::NamedPipe),
        "vsock" => Ok(IpcAddrTag::Vsock),
        _ => Err(E::unknown_variant(value, IPC_ADDR_VARIANTS)),
      }
    }

    #[inline]
    fn visit_bytes<E>(self, value: &[u8]) -> Result<Self::Value, E>
    where
      E: de::Error,
    {
      match value {
        b"unix" => Ok(IpcAddrTag::Unix),
        b"abstract" => Ok(IpcAddrTag::Abstract),
        b"named_pipe" => Ok(IpcAddrTag::NamedPipe),
        b"vsock" => Ok(IpcAddrTag::Vsock),
        _ => Err(E::invalid_value(de::Unexpected::Bytes(value), &self)),
      }
    }

    #[inline]
    fn visit_u8<E>(self, value: u8) -> Result<Self::Value, E>
    where
      E: de::Error,
    {
      self.visit_u64(u64::from(value))
    }

    #[inline]
    fn visit_u16<E>(self, value: u16) -> Result<Self::Value, E>
    where
      E: de::Error,
    {
      self.visit_u64(u64::from(value))
    }

    #[inline]
    fn visit_u32<E>(self, value: u32) -> Result<Self::Value, E>
    where
      E: de::Error,
    {
      self.visit_u64(u64::from(value))
    }

    #[inline]
    fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
    where
      E: de::Error,
    {
      match value {
        0 => Ok(IpcAddrTag::Unix),
        1 => Ok(IpcAddrTag::Abstract),
        2 => Ok(IpcAddrTag::NamedPipe),
        3 => Ok(IpcAddrTag::Vsock),
        _ => Err(E::invalid_value(de::Unexpected::Unsigned(value), &self)),
      }
    }
  }

  #[cfg(target_os = "linux")]
  impl<P, A> Serialize for IpcAddr<P, A>
  where
    P: Serialize,
    A: Serialize,
  {
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
      S: Serializer,
    {
      let mut tuple = serializer.serialize_tuple(2)?;
      match self {
        Self::Unix(addr) => {
          tuple.serialize_element(&IpcAddrTag::Unix)?;
          tuple.serialize_element(addr.as_inner())?;
        }
        Self::Abstract(addr) => {
          tuple.serialize_element(&IpcAddrTag::Abstract)?;
          tuple.serialize_element(addr.as_inner())?;
        }
        #[cfg(feature = "vsock")]
        Self::Vsock(addr) => {
          tuple.serialize_element(&IpcAddrTag::Vsock)?;
          tuple.serialize_element(addr)?;
        }
      }
      tuple.end()
    }
  }

  #[cfg(all(unix, not(target_os = "linux")))]
  impl<P, A> Serialize for IpcAddr<P, A>
  where
    P: Serialize,
  {
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
      S: Serializer,
    {
      let mut tuple = serializer.serialize_tuple(2)?;
      match self {
        Self::Unix(addr) => {
          tuple.serialize_element(&IpcAddrTag::Unix)?;
          tuple.serialize_element(addr.as_inner())?;
        }
        Self::__NonExhaustive(never, _) => match *never {},
      }
      tuple.end()
    }
  }

  #[cfg(windows)]
  impl<P, A> Serialize for IpcAddr<P, A>
  where
    P: Serialize,
  {
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
      S: Serializer,
    {
      let mut tuple = serializer.serialize_tuple(2)?;
      match self {
        Self::NamedPipe(addr) => {
          tuple.serialize_element(&IpcAddrTag::NamedPipe)?;
          tuple.serialize_element(addr.as_inner())?;
        }
        Self::__NonExhaustive(never, _) => match *never {},
      }
      tuple.end()
    }
  }

  #[cfg(all(not(unix), not(windows)))]
  impl<P, A> Serialize for IpcAddr<P, A> {
    #[inline]
    fn serialize<S>(&self, _serializer: S) -> Result<S::Ok, S::Error>
    where
      S: Serializer,
    {
      match self {
        Self::__NonExhaustive(never, _) => match *never {},
      }
    }
  }

  #[cfg(target_os = "linux")]
  impl<'de, P, A> Deserialize<'de> for IpcAddr<P, A>
  where
    P: Deserialize<'de>,
    A: Deserialize<'de>,
  {
    #[inline]
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
      D: Deserializer<'de>,
    {
      deserializer.deserialize_tuple(2, IpcAddrVisitor::new())
    }
  }

  #[cfg(all(unix, not(target_os = "linux")))]
  impl<'de, P, A> Deserialize<'de> for IpcAddr<P, A>
  where
    P: Deserialize<'de>,
  {
    #[inline]
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
      D: Deserializer<'de>,
    {
      deserializer.deserialize_tuple(2, IpcAddrVisitor::new())
    }
  }

  #[cfg(windows)]
  impl<'de, P, A> Deserialize<'de> for IpcAddr<P, A>
  where
    P: Deserialize<'de>,
  {
    #[inline]
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
      D: Deserializer<'de>,
    {
      deserializer.deserialize_tuple(2, IpcAddrVisitor::new())
    }
  }

  #[cfg(all(not(unix), not(windows)))]
  impl<'de, P, A> Deserialize<'de> for IpcAddr<P, A> {
    #[inline]
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
      D: Deserializer<'de>,
    {
      deserializer.deserialize_tuple(2, IpcAddrVisitor::new())
    }
  }

  impl<P, A> IpcAddrVisitor<P, A> {
    #[inline]
    const fn new() -> Self {
      Self {
        marker: PhantomData,
      }
    }
  }

  #[cfg(target_os = "linux")]
  impl<'de, P, A> Visitor<'de> for IpcAddrVisitor<P, A>
  where
    P: Deserialize<'de>,
    A: Deserialize<'de>,
  {
    type Value = IpcAddr<P, A>;

    #[inline]
    fn expecting(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
      formatter.write_str("a two-element IPC address tuple")
    }

    #[inline]
    fn visit_seq<S>(self, mut seq: S) -> Result<Self::Value, S::Error>
    where
      S: de::SeqAccess<'de>,
    {
      let tag: IpcAddrTag = seq
        .next_element()?
        .ok_or_else(|| de::Error::invalid_length(0, &self))?;

      match tag {
        IpcAddrTag::Unix => {
          let value = seq
            .next_element()?
            .ok_or_else(|| de::Error::invalid_length(1, &self))?;
          Ok(IpcAddr::Unix(UnixAddr::new(value)))
        }
        IpcAddrTag::Abstract => {
          let value = seq
            .next_element()?
            .ok_or_else(|| de::Error::invalid_length(1, &self))?;
          Ok(IpcAddr::Abstract(AbstractAddr::new(value)))
        }
        IpcAddrTag::NamedPipe => Err(de::Error::custom(
          "Windows named-pipe IPC addresses are unsupported on this target",
        )),
        IpcAddrTag::Vsock => {
          #[cfg(feature = "vsock")]
          {
            let value = seq
              .next_element()?
              .ok_or_else(|| de::Error::invalid_length(1, &self))?;
            Ok(IpcAddr::Vsock(value))
          }
          #[cfg(not(feature = "vsock"))]
          {
            Err(de::Error::custom(
              "VM socket IPC addresses require the vsock feature on Linux",
            ))
          }
        }
      }
    }
  }

  #[cfg(all(unix, not(target_os = "linux")))]
  impl<'de, P, A> Visitor<'de> for IpcAddrVisitor<P, A>
  where
    P: Deserialize<'de>,
  {
    type Value = IpcAddr<P, A>;

    #[inline]
    fn expecting(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
      formatter.write_str("a two-element IPC address tuple")
    }

    #[inline]
    fn visit_seq<S>(self, mut seq: S) -> Result<Self::Value, S::Error>
    where
      S: de::SeqAccess<'de>,
    {
      let tag: IpcAddrTag = seq
        .next_element()?
        .ok_or_else(|| de::Error::invalid_length(0, &self))?;

      match tag {
        IpcAddrTag::Unix => {
          let value = seq
            .next_element()?
            .ok_or_else(|| de::Error::invalid_length(1, &self))?;
          Ok(IpcAddr::Unix(UnixAddr::new(value)))
        }
        IpcAddrTag::Abstract => Err(de::Error::custom(
          "Linux abstract IPC addresses are unsupported on this target",
        )),
        IpcAddrTag::NamedPipe => Err(de::Error::custom(
          "Windows named-pipe IPC addresses are unsupported on this target",
        )),
        IpcAddrTag::Vsock => Err(de::Error::custom(
          "VM socket IPC addresses require the vsock feature on Linux",
        )),
      }
    }
  }

  #[cfg(windows)]
  impl<'de, P, A> Visitor<'de> for IpcAddrVisitor<P, A>
  where
    P: Deserialize<'de>,
  {
    type Value = IpcAddr<P, A>;

    #[inline]
    fn expecting(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
      formatter.write_str("a two-element IPC address tuple")
    }

    #[inline]
    fn visit_seq<S>(self, mut seq: S) -> Result<Self::Value, S::Error>
    where
      S: de::SeqAccess<'de>,
    {
      let tag: IpcAddrTag = seq
        .next_element()?
        .ok_or_else(|| de::Error::invalid_length(0, &self))?;

      match tag {
        IpcAddrTag::Unix => Err(de::Error::custom(
          "Unix IPC addresses are unsupported on this target",
        )),
        IpcAddrTag::Abstract => Err(de::Error::custom(
          "Linux abstract IPC addresses are unsupported on this target",
        )),
        IpcAddrTag::NamedPipe => {
          let value = seq
            .next_element()?
            .ok_or_else(|| de::Error::invalid_length(1, &self))?;
          Ok(IpcAddr::NamedPipe(NamedPipeAddr::new(value)))
        }
        IpcAddrTag::Vsock => Err(de::Error::custom(
          "VM socket IPC addresses require the vsock feature on Linux",
        )),
      }
    }
  }

  #[cfg(all(not(unix), not(windows)))]
  impl<'de, P, A> Visitor<'de> for IpcAddrVisitor<P, A> {
    type Value = IpcAddr<P, A>;

    #[inline]
    fn expecting(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
      formatter.write_str("a two-element IPC address tuple")
    }

    #[inline]
    fn visit_seq<S>(self, mut seq: S) -> Result<Self::Value, S::Error>
    where
      S: de::SeqAccess<'de>,
    {
      let tag: IpcAddrTag = seq
        .next_element()?
        .ok_or_else(|| de::Error::invalid_length(0, &self))?;

      match tag {
        IpcAddrTag::Unix => Err(de::Error::custom(
          "Unix IPC addresses are unsupported on this target",
        )),
        IpcAddrTag::Abstract => Err(de::Error::custom(
          "Linux abstract IPC addresses are unsupported on this target",
        )),
        IpcAddrTag::NamedPipe => Err(de::Error::custom(
          "Windows named-pipe IPC addresses are unsupported on this target",
        )),
        IpcAddrTag::Vsock => Err(de::Error::custom(
          "VM socket IPC addresses require the vsock feature on Linux",
        )),
      }
    }
  }

  const ADDR_VARIANTS: &[&str] = &["host", "ipc"];

  impl AddrVariant {
    #[inline]
    const fn as_str(self) -> &'static str {
      match self {
        Self::Host => "host",
        Self::Ipc => "ipc",
      }
    }

    #[inline]
    const fn as_u8(self) -> u8 {
      match self {
        Self::Host => 0,
        Self::Ipc => 1,
      }
    }
  }

  impl Serialize for AddrVariant {
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
      S: Serializer,
    {
      if serializer.is_human_readable() {
        serializer.serialize_str((*self).as_str())
      } else {
        serializer.serialize_u8((*self).as_u8())
      }
    }
  }

  impl<H, P, A> Serialize for Addr<H, P, A>
  where
    HostAddr<H>: Serialize,
    IpcAddr<P, A>: Serialize,
  {
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
      S: Serializer,
    {
      if serializer.is_human_readable() {
        match self {
          Self::Host(addr) => serializer.serialize_newtype_variant("Addr", 0, "host", addr),
          Self::Ipc(addr) => serializer.serialize_newtype_variant("Addr", 1, "ipc", addr),
        }
      } else {
        let mut tuple = serializer.serialize_tuple(2)?;
        match self {
          Self::Host(addr) => {
            tuple.serialize_element(&AddrVariant::Host)?;
            tuple.serialize_element(addr)?;
          }
          Self::Ipc(addr) => {
            tuple.serialize_element(&AddrVariant::Ipc)?;
            tuple.serialize_element(addr)?;
          }
        }
        tuple.end()
      }
    }
  }

  impl<'de, H, P, A> Deserialize<'de> for Addr<H, P, A>
  where
    HostAddr<H>: Deserialize<'de>,
    IpcAddr<P, A>: Deserialize<'de>,
  {
    #[inline]
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
      D: Deserializer<'de>,
    {
      if deserializer.is_human_readable() {
        deserializer.deserialize_enum("Addr", ADDR_VARIANTS, AddrVisitor::new())
      } else {
        deserializer.deserialize_tuple(2, AddrVisitor::new())
      }
    }
  }

  impl<'de> Deserialize<'de> for AddrVariant {
    #[inline]
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
      D: Deserializer<'de>,
    {
      if deserializer.is_human_readable() {
        deserializer.deserialize_identifier(AddrVariantVisitor)
      } else {
        deserializer.deserialize_u8(AddrVariantVisitor)
      }
    }
  }

  impl Visitor<'_> for AddrVariantVisitor {
    type Value = AddrVariant;

    #[inline]
    fn expecting(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
      formatter.write_str("an address kind")
    }

    #[inline]
    fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
    where
      E: de::Error,
    {
      match value {
        "host" => Ok(AddrVariant::Host),
        "ipc" => Ok(AddrVariant::Ipc),
        _ => Err(E::unknown_variant(value, ADDR_VARIANTS)),
      }
    }

    #[inline]
    fn visit_bytes<E>(self, value: &[u8]) -> Result<Self::Value, E>
    where
      E: de::Error,
    {
      match value {
        b"host" => Ok(AddrVariant::Host),
        b"ipc" => Ok(AddrVariant::Ipc),
        _ => match core::str::from_utf8(value) {
          Ok(value) => Err(E::unknown_variant(value, ADDR_VARIANTS)),
          Err(_) => Err(E::invalid_value(de::Unexpected::Bytes(value), &self)),
        },
      }
    }

    #[inline]
    fn visit_u8<E>(self, value: u8) -> Result<Self::Value, E>
    where
      E: de::Error,
    {
      self.visit_u64(u64::from(value))
    }

    #[inline]
    fn visit_u16<E>(self, value: u16) -> Result<Self::Value, E>
    where
      E: de::Error,
    {
      self.visit_u64(u64::from(value))
    }

    #[inline]
    fn visit_u32<E>(self, value: u32) -> Result<Self::Value, E>
    where
      E: de::Error,
    {
      self.visit_u64(u64::from(value))
    }

    #[inline]
    fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
    where
      E: de::Error,
    {
      match value {
        0 => Ok(AddrVariant::Host),
        1 => Ok(AddrVariant::Ipc),
        _ => Err(E::invalid_value(de::Unexpected::Unsigned(value), &self)),
      }
    }
  }

  impl<H, P, A> AddrVisitor<H, P, A> {
    #[inline]
    const fn new() -> Self {
      Self {
        marker: PhantomData,
      }
    }
  }

  impl<'de, H, P, A> Visitor<'de> for AddrVisitor<H, P, A>
  where
    HostAddr<H>: Deserialize<'de>,
    IpcAddr<P, A>: Deserialize<'de>,
  {
    type Value = Addr<H, P, A>;

    #[inline]
    fn expecting(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
      formatter.write_str("an externally tagged address or two-element address tuple")
    }

    #[inline]
    fn visit_enum<E>(self, data: E) -> Result<Self::Value, E::Error>
    where
      E: de::EnumAccess<'de>,
    {
      let (variant, access) = data.variant()?;
      match variant {
        AddrVariant::Host => access.newtype_variant().map(Addr::Host),
        AddrVariant::Ipc => access.newtype_variant().map(Addr::Ipc),
      }
    }

    #[inline]
    fn visit_seq<S>(self, mut seq: S) -> Result<Self::Value, S::Error>
    where
      S: de::SeqAccess<'de>,
    {
      let tag: AddrVariant = seq
        .next_element()?
        .ok_or_else(|| de::Error::invalid_length(0, &self))?;

      match tag {
        AddrVariant::Host => seq
          .next_element()?
          .map(Addr::Host)
          .ok_or_else(|| de::Error::invalid_length(1, &self)),
        AddrVariant::Ipc => seq
          .next_element()?
          .map(Addr::Ipc)
          .ok_or_else(|| de::Error::invalid_length(1, &self)),
      }
    }
  }

  impl<P, A> LocalAddrVisitor<P, A> {
    #[inline]
    const fn new() -> Self {
      Self {
        marker: PhantomData,
      }
    }
  }

  impl<'de, P, A> Visitor<'de> for LocalAddrVisitor<P, A>
  where
    LoopbackAddr: Deserialize<'de>,
    IpcAddr<P, A>: Deserialize<'de>,
  {
    type Value = LocalAddr<P, A>;

    #[inline]
    fn expecting(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
      formatter.write_str("an externally tagged local address or two-element local-address tuple")
    }

    #[inline]
    fn visit_enum<E>(self, data: E) -> Result<Self::Value, E::Error>
    where
      E: EnumAccess<'de>,
    {
      let (variant, access) = data.variant()?;
      match variant {
        LocalAddrVariant::Loopback => access.newtype_variant().map(LocalAddr::Loopback),
        LocalAddrVariant::Ipc => access.newtype_variant().map(LocalAddr::Ipc),
      }
    }

    #[inline]
    fn visit_seq<S>(self, mut seq: S) -> Result<Self::Value, S::Error>
    where
      S: de::SeqAccess<'de>,
    {
      let tag: LocalAddrVariant = seq
        .next_element()?
        .ok_or_else(|| de::Error::invalid_length(0, &self))?;

      match tag {
        LocalAddrVariant::Loopback => seq
          .next_element()?
          .map(LocalAddr::Loopback)
          .ok_or_else(|| de::Error::invalid_length(1, &self)),
        LocalAddrVariant::Ipc => seq
          .next_element()?
          .map(LocalAddr::Ipc)
          .ok_or_else(|| de::Error::invalid_length(1, &self)),
      }
    }
  }

  const LOCAL_ADDR_VARIANTS: &[&str] = &["loopback", "ipc"];

  impl LocalAddrVariant {
    #[inline]
    const fn as_str(self) -> &'static str {
      match self {
        Self::Loopback => "loopback",
        Self::Ipc => "ipc",
      }
    }

    #[inline]
    const fn as_u8(self) -> u8 {
      match self {
        Self::Loopback => 0,
        Self::Ipc => 1,
      }
    }
  }

  impl Serialize for LocalAddrVariant {
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
      S: Serializer,
    {
      if serializer.is_human_readable() {
        serializer.serialize_str((*self).as_str())
      } else {
        serializer.serialize_u8((*self).as_u8())
      }
    }
  }

  impl<P, A> Serialize for LocalAddr<P, A>
  where
    LoopbackAddr: Serialize,
    IpcAddr<P, A>: Serialize,
  {
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
      S: Serializer,
    {
      if serializer.is_human_readable() {
        match self {
          Self::Loopback(addr) => {
            serializer.serialize_newtype_variant("LocalAddr", 0, "loopback", addr)
          }
          Self::Ipc(addr) => serializer.serialize_newtype_variant("LocalAddr", 1, "ipc", addr),
        }
      } else {
        let mut tuple = serializer.serialize_tuple(2)?;
        match self {
          Self::Loopback(addr) => {
            tuple.serialize_element(&LocalAddrVariant::Loopback)?;
            tuple.serialize_element(addr)?;
          }
          Self::Ipc(addr) => {
            tuple.serialize_element(&LocalAddrVariant::Ipc)?;
            tuple.serialize_element(addr)?;
          }
        }
        tuple.end()
      }
    }
  }

  impl<'de, P, A> Deserialize<'de> for LocalAddr<P, A>
  where
    LoopbackAddr: Deserialize<'de>,
    IpcAddr<P, A>: Deserialize<'de>,
  {
    #[inline]
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
      D: Deserializer<'de>,
    {
      if deserializer.is_human_readable() {
        deserializer.deserialize_enum("LocalAddr", LOCAL_ADDR_VARIANTS, LocalAddrVisitor::new())
      } else {
        deserializer.deserialize_tuple(2, LocalAddrVisitor::new())
      }
    }
  }

  impl<'de> Deserialize<'de> for LocalAddrVariant {
    #[inline]
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
      D: Deserializer<'de>,
    {
      if deserializer.is_human_readable() {
        deserializer.deserialize_identifier(LocalAddrVariantVisitor)
      } else {
        deserializer.deserialize_u8(LocalAddrVariantVisitor)
      }
    }
  }

  impl Visitor<'_> for LocalAddrVariantVisitor {
    type Value = LocalAddrVariant;

    #[inline]
    fn expecting(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
      formatter.write_str("a local-address kind")
    }

    #[inline]
    fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
    where
      E: de::Error,
    {
      match value {
        "loopback" => Ok(LocalAddrVariant::Loopback),
        "ipc" => Ok(LocalAddrVariant::Ipc),
        _ => Err(E::unknown_variant(value, LOCAL_ADDR_VARIANTS)),
      }
    }

    #[inline]
    fn visit_bytes<E>(self, value: &[u8]) -> Result<Self::Value, E>
    where
      E: de::Error,
    {
      match value {
        b"loopback" => Ok(LocalAddrVariant::Loopback),
        b"ipc" => Ok(LocalAddrVariant::Ipc),
        _ => match core::str::from_utf8(value) {
          Ok(value) => Err(E::unknown_variant(value, LOCAL_ADDR_VARIANTS)),
          Err(_) => Err(E::invalid_value(de::Unexpected::Bytes(value), &self)),
        },
      }
    }

    #[inline]
    fn visit_u8<E>(self, value: u8) -> Result<Self::Value, E>
    where
      E: de::Error,
    {
      self.visit_u64(u64::from(value))
    }

    #[inline]
    fn visit_u16<E>(self, value: u16) -> Result<Self::Value, E>
    where
      E: de::Error,
    {
      self.visit_u64(u64::from(value))
    }

    #[inline]
    fn visit_u32<E>(self, value: u32) -> Result<Self::Value, E>
    where
      E: de::Error,
    {
      self.visit_u64(u64::from(value))
    }

    #[inline]
    fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
    where
      E: de::Error,
    {
      match value {
        0 => Ok(LocalAddrVariant::Loopback),
        1 => Ok(LocalAddrVariant::Ipc),
        _ => Err(E::invalid_value(de::Unexpected::Unsigned(value), &self)),
      }
    }
  }
};
