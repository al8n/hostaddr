#[cfg(all(feature = "std", any(unix, windows)))]
use std::path::Path;

use crate::{HostAddr, LoopbackAddr};
#[cfg(feature = "serde")]
use serde::de::VariantAccess as _;

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

#[cfg(feature = "serde")]
const ADDR_VARIANTS: &[&str] = &["host", "ipc"];

#[cfg(feature = "serde")]
type AddrVisitorMarker<H, P, A> = core::marker::PhantomData<fn() -> (H, P, A)>;

#[cfg(feature = "serde")]
impl<H, P, A> serde::Serialize for Addr<H, P, A>
where
  HostAddr<H>: serde::Serialize,
  IpcAddr<P, A>: serde::Serialize,
{
  #[inline]
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
    S: serde::Serializer,
  {
    match self {
      Self::Host(addr) => serializer.serialize_newtype_variant("Addr", 0, "host", addr),
      Self::Ipc(addr) => serializer.serialize_newtype_variant("Addr", 1, "ipc", addr),
    }
  }
}

#[cfg(feature = "serde")]
impl<'de, H, P, A> serde::Deserialize<'de> for Addr<H, P, A>
where
  HostAddr<H>: serde::Deserialize<'de>,
  IpcAddr<P, A>: serde::Deserialize<'de>,
{
  #[inline]
  fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
  where
    D: serde::Deserializer<'de>,
  {
    deserializer.deserialize_enum("Addr", ADDR_VARIANTS, AddrVisitor::new())
  }
}

#[cfg(feature = "serde")]
enum AddrVariant {
  Host,
  Ipc,
}

#[cfg(feature = "serde")]
impl<'de> serde::Deserialize<'de> for AddrVariant {
  #[inline]
  fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
  where
    D: serde::Deserializer<'de>,
  {
    deserializer.deserialize_identifier(AddrVariantVisitor)
  }
}

#[cfg(feature = "serde")]
struct AddrVariantVisitor;

#[cfg(feature = "serde")]
impl serde::de::Visitor<'_> for AddrVariantVisitor {
  type Value = AddrVariant;

  #[inline]
  fn expecting(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    formatter.write_str("an address kind")
  }

  #[inline]
  fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
  where
    E: serde::de::Error,
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
    E: serde::de::Error,
  {
    match value {
      b"host" => Ok(AddrVariant::Host),
      b"ipc" => Ok(AddrVariant::Ipc),
      _ => match core::str::from_utf8(value) {
        Ok(value) => Err(E::unknown_variant(value, ADDR_VARIANTS)),
        Err(_) => Err(E::invalid_value(serde::de::Unexpected::Bytes(value), &self)),
      },
    }
  }

  #[inline]
  fn visit_u8<E>(self, value: u8) -> Result<Self::Value, E>
  where
    E: serde::de::Error,
  {
    self.visit_u64(u64::from(value))
  }

  #[inline]
  fn visit_u16<E>(self, value: u16) -> Result<Self::Value, E>
  where
    E: serde::de::Error,
  {
    self.visit_u64(u64::from(value))
  }

  #[inline]
  fn visit_u32<E>(self, value: u32) -> Result<Self::Value, E>
  where
    E: serde::de::Error,
  {
    self.visit_u64(u64::from(value))
  }

  #[inline]
  fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
  where
    E: serde::de::Error,
  {
    match value {
      0 => Ok(AddrVariant::Host),
      1 => Ok(AddrVariant::Ipc),
      _ => Err(E::invalid_value(
        serde::de::Unexpected::Unsigned(value),
        &self,
      )),
    }
  }
}

#[cfg(feature = "serde")]
struct AddrVisitor<H, P, A> {
  marker: AddrVisitorMarker<H, P, A>,
}

#[cfg(feature = "serde")]
impl<H, P, A> AddrVisitor<H, P, A> {
  #[inline]
  const fn new() -> Self {
    Self {
      marker: core::marker::PhantomData,
    }
  }
}

#[cfg(feature = "serde")]
impl<'de, H, P, A> serde::de::Visitor<'de> for AddrVisitor<H, P, A>
where
  HostAddr<H>: serde::Deserialize<'de>,
  IpcAddr<P, A>: serde::Deserialize<'de>,
{
  type Value = Addr<H, P, A>;

  #[inline]
  fn expecting(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    formatter.write_str("an externally tagged address")
  }

  #[inline]
  fn visit_enum<E>(self, data: E) -> Result<Self::Value, E::Error>
  where
    E: serde::de::EnumAccess<'de>,
  {
    let (variant, access) = data.variant()?;
    match variant {
      AddrVariant::Host => access.newtype_variant().map(Addr::Host),
      AddrVariant::Ipc => access.newtype_variant().map(Addr::Ipc),
    }
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
  __NonExhaustive(
    core::convert::Infallible,
    core::marker::PhantomData<fn() -> (P, A)>,
  ),
}

#[cfg(feature = "serde")]
const IPC_ADDR_VARIANTS: &[&str] = &["unix", "abstract", "named_pipe", "vsock"];

#[cfg(feature = "serde")]
enum IpcAddrTag {
  Unix,
  Abstract,
  NamedPipe,
  Vsock,
}

#[cfg(feature = "serde")]
impl<'de> serde::Deserialize<'de> for IpcAddrTag {
  #[inline]
  fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
  where
    D: serde::Deserializer<'de>,
  {
    deserializer.deserialize_str(IpcAddrTagVisitor)
  }
}

#[cfg(feature = "serde")]
struct IpcAddrTagVisitor;

#[cfg(feature = "serde")]
impl serde::de::Visitor<'_> for IpcAddrTagVisitor {
  type Value = IpcAddrTag;

  #[inline]
  fn expecting(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    formatter.write_str("an IPC address kind")
  }

  #[inline]
  fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
  where
    E: serde::de::Error,
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
    E: serde::de::Error,
  {
    match value {
      b"unix" => Ok(IpcAddrTag::Unix),
      b"abstract" => Ok(IpcAddrTag::Abstract),
      b"named_pipe" => Ok(IpcAddrTag::NamedPipe),
      b"vsock" => Ok(IpcAddrTag::Vsock),
      _ => Err(E::invalid_value(serde::de::Unexpected::Bytes(value), &self)),
    }
  }
}

#[cfg(all(feature = "serde", target_os = "linux"))]
impl<P, A> serde::Serialize for IpcAddr<P, A>
where
  P: serde::Serialize,
  A: serde::Serialize,
{
  #[inline]
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
    S: serde::Serializer,
  {
    use serde::ser::SerializeTuple;

    let mut tuple = serializer.serialize_tuple(2)?;
    match self {
      Self::Unix(addr) => {
        tuple.serialize_element("unix")?;
        tuple.serialize_element(addr.as_inner())?;
      }
      Self::Abstract(addr) => {
        tuple.serialize_element("abstract")?;
        tuple.serialize_element(addr.as_inner())?;
      }
      #[cfg(feature = "vsock")]
      Self::Vsock(addr) => {
        tuple.serialize_element("vsock")?;
        tuple.serialize_element(addr)?;
      }
    }
    tuple.end()
  }
}

#[cfg(all(feature = "serde", unix, not(target_os = "linux")))]
impl<P, A> serde::Serialize for IpcAddr<P, A>
where
  P: serde::Serialize,
{
  #[inline]
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
    S: serde::Serializer,
  {
    use serde::ser::SerializeTuple;

    let mut tuple = serializer.serialize_tuple(2)?;
    match self {
      Self::Unix(addr) => {
        tuple.serialize_element("unix")?;
        tuple.serialize_element(addr.as_inner())?;
      }
      Self::__NonExhaustive(never, _) => match *never {},
    }
    tuple.end()
  }
}

#[cfg(all(feature = "serde", windows))]
impl<P, A> serde::Serialize for IpcAddr<P, A>
where
  P: serde::Serialize,
{
  #[inline]
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
    S: serde::Serializer,
  {
    use serde::ser::SerializeTuple;

    let mut tuple = serializer.serialize_tuple(2)?;
    match self {
      Self::NamedPipe(addr) => {
        tuple.serialize_element("named_pipe")?;
        tuple.serialize_element(addr.as_inner())?;
      }
      Self::__NonExhaustive(never, _) => match *never {},
    }
    tuple.end()
  }
}

#[cfg(all(feature = "serde", not(unix), not(windows)))]
impl<P, A> serde::Serialize for IpcAddr<P, A> {
  #[inline]
  fn serialize<S>(&self, _serializer: S) -> Result<S::Ok, S::Error>
  where
    S: serde::Serializer,
  {
    match self {
      Self::__NonExhaustive(never, _) => match *never {},
    }
  }
}

#[cfg(all(feature = "serde", target_os = "linux"))]
impl<'de, P, A> serde::Deserialize<'de> for IpcAddr<P, A>
where
  P: serde::Deserialize<'de>,
  A: serde::Deserialize<'de>,
{
  #[inline]
  fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
  where
    D: serde::Deserializer<'de>,
  {
    deserializer.deserialize_tuple(2, IpcAddrVisitor::new())
  }
}

#[cfg(all(feature = "serde", unix, not(target_os = "linux")))]
impl<'de, P, A> serde::Deserialize<'de> for IpcAddr<P, A>
where
  P: serde::Deserialize<'de>,
{
  #[inline]
  fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
  where
    D: serde::Deserializer<'de>,
  {
    deserializer.deserialize_tuple(2, IpcAddrVisitor::new())
  }
}

#[cfg(all(feature = "serde", windows))]
impl<'de, P, A> serde::Deserialize<'de> for IpcAddr<P, A>
where
  P: serde::Deserialize<'de>,
{
  #[inline]
  fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
  where
    D: serde::Deserializer<'de>,
  {
    deserializer.deserialize_tuple(2, IpcAddrVisitor::new())
  }
}

#[cfg(all(feature = "serde", not(unix), not(windows)))]
impl<'de, P, A> serde::Deserialize<'de> for IpcAddr<P, A> {
  #[inline]
  fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
  where
    D: serde::Deserializer<'de>,
  {
    deserializer.deserialize_tuple(2, IpcAddrVisitor::new())
  }
}

#[cfg(feature = "serde")]
struct IpcAddrVisitor<P, A> {
  marker: core::marker::PhantomData<fn() -> (P, A)>,
}

#[cfg(feature = "serde")]
impl<P, A> IpcAddrVisitor<P, A> {
  #[inline]
  const fn new() -> Self {
    Self {
      marker: core::marker::PhantomData,
    }
  }
}

#[cfg(all(feature = "serde", target_os = "linux"))]
impl<'de, P, A> serde::de::Visitor<'de> for IpcAddrVisitor<P, A>
where
  P: serde::Deserialize<'de>,
  A: serde::Deserialize<'de>,
{
  type Value = IpcAddr<P, A>;

  #[inline]
  fn expecting(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    formatter.write_str("a two-element IPC address tuple")
  }

  #[inline]
  fn visit_seq<S>(self, mut seq: S) -> Result<Self::Value, S::Error>
  where
    S: serde::de::SeqAccess<'de>,
  {
    let tag: IpcAddrTag = seq
      .next_element()?
      .ok_or_else(|| serde::de::Error::invalid_length(0, &self))?;

    match tag {
      IpcAddrTag::Unix => {
        let value = seq
          .next_element()?
          .ok_or_else(|| serde::de::Error::invalid_length(1, &self))?;
        Ok(IpcAddr::Unix(UnixAddr::new(value)))
      }
      IpcAddrTag::Abstract => {
        let value = seq
          .next_element()?
          .ok_or_else(|| serde::de::Error::invalid_length(1, &self))?;
        Ok(IpcAddr::Abstract(AbstractAddr::new(value)))
      }
      IpcAddrTag::NamedPipe => Err(serde::de::Error::custom(
        "Windows named-pipe IPC addresses are unsupported on this target",
      )),
      IpcAddrTag::Vsock => {
        #[cfg(feature = "vsock")]
        {
          let value = seq
            .next_element()?
            .ok_or_else(|| serde::de::Error::invalid_length(1, &self))?;
          Ok(IpcAddr::Vsock(value))
        }
        #[cfg(not(feature = "vsock"))]
        {
          Err(serde::de::Error::custom(
            "VM socket IPC addresses require the vsock feature on Linux",
          ))
        }
      }
    }
  }
}

#[cfg(all(feature = "serde", unix, not(target_os = "linux")))]
impl<'de, P, A> serde::de::Visitor<'de> for IpcAddrVisitor<P, A>
where
  P: serde::Deserialize<'de>,
{
  type Value = IpcAddr<P, A>;

  #[inline]
  fn expecting(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    formatter.write_str("a two-element IPC address tuple")
  }

  #[inline]
  fn visit_seq<S>(self, mut seq: S) -> Result<Self::Value, S::Error>
  where
    S: serde::de::SeqAccess<'de>,
  {
    let tag: IpcAddrTag = seq
      .next_element()?
      .ok_or_else(|| serde::de::Error::invalid_length(0, &self))?;

    match tag {
      IpcAddrTag::Unix => {
        let value = seq
          .next_element()?
          .ok_or_else(|| serde::de::Error::invalid_length(1, &self))?;
        Ok(IpcAddr::Unix(UnixAddr::new(value)))
      }
      IpcAddrTag::Abstract => Err(serde::de::Error::custom(
        "Linux abstract IPC addresses are unsupported on this target",
      )),
      IpcAddrTag::NamedPipe => Err(serde::de::Error::custom(
        "Windows named-pipe IPC addresses are unsupported on this target",
      )),
      IpcAddrTag::Vsock => Err(serde::de::Error::custom(
        "VM socket IPC addresses require the vsock feature on Linux",
      )),
    }
  }
}

#[cfg(all(feature = "serde", windows))]
impl<'de, P, A> serde::de::Visitor<'de> for IpcAddrVisitor<P, A>
where
  P: serde::Deserialize<'de>,
{
  type Value = IpcAddr<P, A>;

  #[inline]
  fn expecting(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    formatter.write_str("a two-element IPC address tuple")
  }

  #[inline]
  fn visit_seq<S>(self, mut seq: S) -> Result<Self::Value, S::Error>
  where
    S: serde::de::SeqAccess<'de>,
  {
    let tag: IpcAddrTag = seq
      .next_element()?
      .ok_or_else(|| serde::de::Error::invalid_length(0, &self))?;

    match tag {
      IpcAddrTag::Unix => Err(serde::de::Error::custom(
        "Unix IPC addresses are unsupported on this target",
      )),
      IpcAddrTag::Abstract => Err(serde::de::Error::custom(
        "Linux abstract IPC addresses are unsupported on this target",
      )),
      IpcAddrTag::NamedPipe => {
        let value = seq
          .next_element()?
          .ok_or_else(|| serde::de::Error::invalid_length(1, &self))?;
        Ok(IpcAddr::NamedPipe(NamedPipeAddr::new(value)))
      }
      IpcAddrTag::Vsock => Err(serde::de::Error::custom(
        "VM socket IPC addresses require the vsock feature on Linux",
      )),
    }
  }
}

#[cfg(all(feature = "serde", not(unix), not(windows)))]
impl<'de, P, A> serde::de::Visitor<'de> for IpcAddrVisitor<P, A> {
  type Value = IpcAddr<P, A>;

  #[inline]
  fn expecting(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    formatter.write_str("a two-element IPC address tuple")
  }

  #[inline]
  fn visit_seq<S>(self, mut seq: S) -> Result<Self::Value, S::Error>
  where
    S: serde::de::SeqAccess<'de>,
  {
    let tag: IpcAddrTag = seq
      .next_element()?
      .ok_or_else(|| serde::de::Error::invalid_length(0, &self))?;

    match tag {
      IpcAddrTag::Unix => Err(serde::de::Error::custom(
        "Unix IPC addresses are unsupported on this target",
      )),
      IpcAddrTag::Abstract => Err(serde::de::Error::custom(
        "Linux abstract IPC addresses are unsupported on this target",
      )),
      IpcAddrTag::NamedPipe => Err(serde::de::Error::custom(
        "Windows named-pipe IPC addresses are unsupported on this target",
      )),
      IpcAddrTag::Vsock => Err(serde::de::Error::custom(
        "VM socket IPC addresses require the vsock feature on Linux",
      )),
    }
  }
}

#[cfg(unix)]
#[cfg_attr(docsrs, doc(cfg(unix)))]
impl<P, A> From<UnixAddr<P>> for IpcAddr<P, A> {
  #[inline]
  fn from(value: UnixAddr<P>) -> Self {
    Self::Unix(value)
  }
}

#[cfg(target_os = "linux")]
#[cfg_attr(docsrs, doc(cfg(target_os = "linux")))]
impl<P, A> From<AbstractAddr<A>> for IpcAddr<P, A> {
  #[inline]
  fn from(value: AbstractAddr<A>) -> Self {
    Self::Abstract(value)
  }
}

#[cfg(windows)]
#[cfg_attr(docsrs, doc(cfg(windows)))]
impl<P, A> From<NamedPipeAddr<P>> for IpcAddr<P, A> {
  #[inline]
  fn from(value: NamedPipeAddr<P>) -> Self {
    Self::NamedPipe(value)
  }
}

#[cfg(all(feature = "vsock", target_os = "linux"))]
#[cfg_attr(docsrs, doc(cfg(all(feature = "vsock", target_os = "linux"))))]
impl<P, A> From<VsockAddr> for IpcAddr<P, A> {
  #[inline]
  fn from(value: VsockAddr) -> Self {
    Self::Vsock(value)
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
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct NamedPipeAddr<P: ?Sized>(P);

#[cfg(windows)]
#[cfg_attr(docsrs, doc(cfg(windows)))]
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

#[cfg(windows)]
#[cfg_attr(docsrs, doc(cfg(windows)))]
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

#[cfg(all(feature = "std", windows))]
#[cfg_attr(docsrs, doc(cfg(all(feature = "std", windows))))]
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

#[cfg(all(feature = "std", windows))]
#[cfg_attr(docsrs, doc(cfg(all(feature = "std", windows))))]
impl NamedPipeAddr<Path> {
  /// Converts a filesystem path reference into a borrowed named-pipe address.
  #[inline]
  pub fn from_path(path: &Path) -> &Self {
    Self::from_ref(path)
  }
}

#[cfg(windows)]
#[cfg_attr(docsrs, doc(cfg(windows)))]
impl<P: ?Sized> core::borrow::Borrow<P> for NamedPipeAddr<P> {
  #[inline]
  fn borrow(&self) -> &P {
    &self.0
  }
}

#[cfg(windows)]
#[cfg_attr(docsrs, doc(cfg(windows)))]
impl<P> From<P> for NamedPipeAddr<P> {
  #[inline]
  fn from(value: P) -> Self {
    Self::new(value)
  }
}

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

#[cfg(target_os = "linux")]
#[cfg_attr(docsrs, doc(cfg(target_os = "linux")))]
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

#[cfg(target_os = "linux")]
#[cfg_attr(docsrs, doc(cfg(target_os = "linux")))]
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

#[cfg(target_os = "linux")]
#[cfg_attr(docsrs, doc(cfg(target_os = "linux")))]
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

#[cfg(target_os = "linux")]
#[cfg_attr(docsrs, doc(cfg(target_os = "linux")))]
impl AbstractAddr<[u8]> {
  /// Converts bytes into a borrowed abstract socket address.
  ///
  /// The input must not include the leading NUL byte used by the kernel.
  #[inline]
  pub const fn from_bytes(name: &[u8]) -> &Self {
    Self::from_ref(name)
  }
}

#[cfg(target_os = "linux")]
#[cfg_attr(docsrs, doc(cfg(target_os = "linux")))]
impl<A: ?Sized> core::borrow::Borrow<A> for AbstractAddr<A> {
  #[inline]
  fn borrow(&self) -> &A {
    &self.0
  }
}

#[cfg(target_os = "linux")]
#[cfg_attr(docsrs, doc(cfg(target_os = "linux")))]
impl<A> From<A> for AbstractAddr<A> {
  #[inline]
  fn from(value: A) -> Self {
    Self::new(value)
  }
}

/// A VM socket address.
#[cfg(all(feature = "vsock", target_os = "linux"))]
#[cfg_attr(docsrs, doc(cfg(all(feature = "vsock", target_os = "linux"))))]
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct VsockAddr {
  cid: u32,
  port: u32,
}

#[cfg(all(feature = "vsock", target_os = "linux"))]
#[cfg_attr(docsrs, doc(cfg(all(feature = "vsock", target_os = "linux"))))]
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

#[cfg(all(feature = "vsock", target_os = "linux"))]
#[cfg_attr(docsrs, doc(cfg(all(feature = "vsock", target_os = "linux"))))]
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

#[cfg(feature = "serde")]
const LOCAL_ADDR_VARIANTS: &[&str] = &["loopback", "ipc"];

#[cfg(feature = "serde")]
impl<P, A> serde::Serialize for LocalAddr<P, A>
where
  LoopbackAddr: serde::Serialize,
  IpcAddr<P, A>: serde::Serialize,
{
  #[inline]
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
    S: serde::Serializer,
  {
    match self {
      Self::Loopback(addr) => {
        serializer.serialize_newtype_variant("LocalAddr", 0, "loopback", addr)
      }
      Self::Ipc(addr) => serializer.serialize_newtype_variant("LocalAddr", 1, "ipc", addr),
    }
  }
}

#[cfg(feature = "serde")]
impl<'de, P, A> serde::Deserialize<'de> for LocalAddr<P, A>
where
  LoopbackAddr: serde::Deserialize<'de>,
  IpcAddr<P, A>: serde::Deserialize<'de>,
{
  #[inline]
  fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
  where
    D: serde::Deserializer<'de>,
  {
    deserializer.deserialize_enum("LocalAddr", LOCAL_ADDR_VARIANTS, LocalAddrVisitor::new())
  }
}

#[cfg(feature = "serde")]
enum LocalAddrVariant {
  Loopback,
  Ipc,
}

#[cfg(feature = "serde")]
impl<'de> serde::Deserialize<'de> for LocalAddrVariant {
  #[inline]
  fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
  where
    D: serde::Deserializer<'de>,
  {
    deserializer.deserialize_identifier(LocalAddrVariantVisitor)
  }
}

#[cfg(feature = "serde")]
struct LocalAddrVariantVisitor;

#[cfg(feature = "serde")]
impl serde::de::Visitor<'_> for LocalAddrVariantVisitor {
  type Value = LocalAddrVariant;

  #[inline]
  fn expecting(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    formatter.write_str("a local-address kind")
  }

  #[inline]
  fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
  where
    E: serde::de::Error,
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
    E: serde::de::Error,
  {
    match value {
      b"loopback" => Ok(LocalAddrVariant::Loopback),
      b"ipc" => Ok(LocalAddrVariant::Ipc),
      _ => match core::str::from_utf8(value) {
        Ok(value) => Err(E::unknown_variant(value, LOCAL_ADDR_VARIANTS)),
        Err(_) => Err(E::invalid_value(serde::de::Unexpected::Bytes(value), &self)),
      },
    }
  }

  #[inline]
  fn visit_u8<E>(self, value: u8) -> Result<Self::Value, E>
  where
    E: serde::de::Error,
  {
    self.visit_u64(u64::from(value))
  }

  #[inline]
  fn visit_u16<E>(self, value: u16) -> Result<Self::Value, E>
  where
    E: serde::de::Error,
  {
    self.visit_u64(u64::from(value))
  }

  #[inline]
  fn visit_u32<E>(self, value: u32) -> Result<Self::Value, E>
  where
    E: serde::de::Error,
  {
    self.visit_u64(u64::from(value))
  }

  #[inline]
  fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
  where
    E: serde::de::Error,
  {
    match value {
      0 => Ok(LocalAddrVariant::Loopback),
      1 => Ok(LocalAddrVariant::Ipc),
      _ => Err(E::invalid_value(
        serde::de::Unexpected::Unsigned(value),
        &self,
      )),
    }
  }
}

#[cfg(feature = "serde")]
struct LocalAddrVisitor<P, A> {
  marker: core::marker::PhantomData<fn() -> (P, A)>,
}

#[cfg(feature = "serde")]
impl<P, A> LocalAddrVisitor<P, A> {
  #[inline]
  const fn new() -> Self {
    Self {
      marker: core::marker::PhantomData,
    }
  }
}

#[cfg(feature = "serde")]
impl<'de, P, A> serde::de::Visitor<'de> for LocalAddrVisitor<P, A>
where
  LoopbackAddr: serde::Deserialize<'de>,
  IpcAddr<P, A>: serde::Deserialize<'de>,
{
  type Value = LocalAddr<P, A>;

  #[inline]
  fn expecting(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    formatter.write_str("an externally tagged local address")
  }

  #[inline]
  fn visit_enum<E>(self, data: E) -> Result<Self::Value, E::Error>
  where
    E: serde::de::EnumAccess<'de>,
  {
    let (variant, access) = data.variant()?;
    match variant {
      LocalAddrVariant::Loopback => access.newtype_variant().map(LocalAddr::Loopback),
      LocalAddrVariant::Ipc => access.newtype_variant().map(LocalAddr::Ipc),
    }
  }
}

#[cfg(test)]
mod tests {
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
}
