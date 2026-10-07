# Address Abstraction Design (v2)

> Status: the core taxonomy below is implemented in the `0.3.x` line and is
> being stabilized for `1.0.0`. `1.0.0-rc.1` was published on 2026-10-07;
> `1.0.0-rc.2` is the current validation target.

## Goals

This design extends `hostaddr` from Internet host addresses to a focused,
type-safe address abstraction for the host and IPC families modeled by this
crate.

Design goals:

* Support both network and IPC transports.
* Support owned and borrowed storage.
* Keep transport kind and locality separate.
* Encode invariants using Rust types.
* Avoid unnecessary allocations.
* Follow the existing `hostaddr` generic-storage philosophy.

---

# Core Address Hierarchy

```rust
pub enum Addr<H, P, A> {
    Host(HostAddr<H>),
    Ipc(IpcAddr<P, A>),
}
```

`Addr` represents the host and IPC address families accepted by this crate. It
is not a claim that every runtime-specific endpoint or protocol is modeled.

Examples:

```text
example.com:443
127.0.0.1:8080
/tmp/app.sock
Linux abstract socket
Windows named pipe
Vsock
```

---

# Host Address

`HostAddr<S>` remains the validated DNS/IP host-address type. It stores a host
and an optional port; it does not store the extra `flowinfo` or `scope_id`
fields present in `SocketAddrV6`.

`Domain`, `Host`, and `HostAddr` retain representation-sensitive, case-sensitive
`Eq`, `Ord`, and `Hash` semantics. DNS-insensitive identity keys must normalize
their input at the call site.

Allocating domain parsers and `verify_domain` decode percent-encoded input,
normalize Unicode through UTS46, and validate ASCII `xn--` A-labels with the
same UTS46 implementation. The structural `try_from_ascii_*` and
`verify_ascii_domain` and `verify_ascii_domain_allow_percent_encoding` entry
points intentionally perform only ASCII label and length checks (after any
percent decoding), so they remain available in no-alloc builds without IDNA
data.

```text
Domain
        ↓
Host
        ↓
HostAddr
```

Examples:

```text
example.com:443
localhost:8080
127.0.0.1:8080
[::1]:8080
```

---

# IPC Address

```rust
pub enum IpcAddr<P, A> {
    Unix(UnixAddr<P>),

    #[cfg(target_os = "linux")]
    Abstract(AbstractAddr<A>),

    #[cfg(windows)]
    NamedPipe(NamedPipeAddr<P>),

    #[cfg(all(feature = "vsock", target_os = "linux"))]
    Vsock(VsockAddr),
}
```

`IpcAddr` represents non-IP communication transports. Its constructors only
wrap the supplied representation: they do not open a socket, inspect the
filesystem, normalize a platform name, or establish a trust boundary.

Unlike previous proposals, it intentionally does **not** contain `SocketAddr` or `HostAddr`.

---

# Unix Address

```rust
pub struct UnixAddr<P: ?Sized>(P);
```

Storage type for the optional filesystem view (when the selected platform
provides that view):

```rust
P: AsRef<Path> (when the `std` feature is enabled)
```

Examples:

```text
/tmp/app.sock
/run/app.sock
```

The constructor itself accepts any storage type and performs no OS-level
pathname validation.

---

# Named Pipe Address

```rust
pub struct NamedPipeAddr<P: ?Sized>(P);
```

Storage type for the optional filesystem view:

```rust
P: AsRef<Path> (when the `std` feature is enabled)
```

Examples:

```text
\\.\pipe\my-service
```

The constructor is a representation wrapper and performs no OS-level named-pipe
validation.

---

# Linux Abstract Address

```rust
pub struct AbstractAddr<A: ?Sized>(A);
```

The payload is interpreted as the name after the kernel's leading-NUL marker.
Construction stores the supplied bytes exactly: it does not add, remove, or
reject a leading or interior NUL. `as_bytes` returns those original bytes.

Storage type:

```rust
A: AsRef<[u8]>
```

For example, the payload:

```text
my.sock
```

is interpreted after the kernel marker as:

```text
\0my.sock
```

This keeps the API platform-independent while leaving byte policy to the caller.

---

# Vsock

```rust
#[cfg(all(feature = "vsock", target_os = "linux"))]
Vsock(VsockAddr)
```

Represents host ↔ VM or VM ↔ VM communication.

The `vsock` feature is enabled by default so existing users get the full local
transport taxonomy unless they opt out with `default-features = false`.

---

# Local Address

```rust
pub enum LocalAddr<P, A> {
    Loopback(LoopbackAddr),
    Ipc(IpcAddr<P, A>),
}
```

`LocalAddr` separates loopback/IP classification from non-IP IPC transport
classification. `LocalAddr::Ipc` is not a proof that an endpoint is same-machine
or safe to use as a security boundary; callers must apply OS-level policy.

Included:

* Loopback IP
* Unix Domain Socket
* Linux Abstract Socket
* Windows Named Pipe
* Vsock

Excluded:

* Link-local
* Private LAN
* Public Internet
* Domains

---

# Loopback Address

```rust
pub struct LoopbackAddr(SocketAddr);
```

Construction:

```rust
impl TryFrom<SocketAddr> for LoopbackAddr;
```

Validation uses:

```rust
iprfc's loopback predicate: 127.0.0.0/8 or ::1
```

Supported:

IPv4:

```text
127.0.0.0/8
```

IPv6:

```text
::1
```

Examples:

```text
127.0.0.1:8080
127.1.2.3:8080
[::1]:8080
```

---

# Type Relationships

```text
Domain<S>
        │
        ▼
Host<S>
        │
        ▼
HostAddr<S>
        │
        ▼
Addr<H, P, A>
├────────────── Host(HostAddr<H>)
└────────────── Ipc(IpcAddr<P, A>)
                      │
                      ├── UnixAddr<P>
                      ├── NamedPipeAddr<P>
                      ├── AbstractAddr<A>
                      └── VsockAddr

LoopbackAddr
        │
        ▼
LocalAddr<P, A>
├────────────── Loopback
└────────────── Ipc(IpcAddr<P, A>)
```

---

# Generic Storage Philosophy

Every address owns only the semantic validation implemented for its family.

Storage is user selectable within the supported trait and feature combinations
for each address family.

Examples:

Owned:

```rust
Addr<String, PathBuf, Vec<u8>>
```

Borrowed:

```rust
Addr<&str, &Path, &[u8]>
```

Inline storage:

```rust
Addr<
    smol_str::SmolStr,
    camino::Utf8PathBuf,
    smallvec::SmallVec<[u8; 32]>,
>
```

The address types never dictate allocation strategy, but a custom storage type
must satisfy the traits required by the specific family and feature set; this
is not an assertion that every custom storage works for every address family.

---

# Conversions

Implemented conversions:

```rust
From<HostAddr<H>> for Addr<H, P, A>

From<IpcAddr<P, A>> for Addr<H, P, A>

From<LoopbackAddr> for LocalAddr<P, A>

From<IpcAddr<P, A>> for LocalAddr<P, A>

TryFrom<SocketAddr> for LoopbackAddr
```

Each refined type validates only its own invariant.

`From<SocketAddrV6> for HostAddr<S>` and `HostAddr::from_sock_addr` keep only
the IP address and port. IPv6 `flowinfo` and `scope_id` are intentionally
discarded; callers that need either field must retain the original
`SocketAddrV6`.

---

# Serde Wire Contract

Serde is optional. Human-readable formats use named address variants and
textual IPC tags. Binary formats use two-element tuples with stable numeric
tags:

| Type | Numeric tags |
| --- | --- |
| `IpcAddr` | `Unix = 0`, `Abstract = 1`, `NamedPipe = 2`, `Vsock = 3` |
| `Addr` | `Host = 0`, `Ipc = 1` |
| `LocalAddr` | `Loopback = 0`, `Ipc = 1` |

The corresponding human-readable names are `unix`, `abstract`, `named_pipe`,
`vsock`, `host`, `ipc`, and `loopback`. These names and tags are part of the
`1.0.0-rc.1` through `1.0.x` compatibility contract. Deserialization must
continue to validate domain and semantic-address invariants rather than
constructing unchecked values.

The contract applies across supported platforms and both human-readable and
binary Serde formats. A variant that is not compiled for the target platform
is rejected during deserialization; its numeric tag is never reinterpreted as
another variant. New variants use new tags and names, and existing tags are
never reused. `Domain` and `Buffer` keep their existing data-model boundary:
human-readable formats carry validated text, while binary formats carry the
validated byte representation. This compatibility promise covers the
`1.0.0-rc.1`/`rc.2` migration and subsequent `1.0.x` releases; it does not
promise compatibility with malformed values produced by pre-1.0 unchecked
constructors.

Semantic IP and socket wrappers are part of the same compatibility contract:

| Model | Validated data | Human-readable writer | Human-readable reader | Binary representation |
| --- | --- | --- | --- | --- |
| `*IpAddr` | `IpAddr` | IP string | IP string | existing `IpAddr` representation |
| `*Addr` V4 | `SocketAddrV4` | `{"v4":{"ip":"...","port":...}}` | RC2 object or RC1 string | tag `0`: `V4(ip, port)` |
| `*Addr` V6 | `SocketAddrV6` | `{"v6":{"ip":"...","port":...,"flowinfo":...,"scope_id":...}}` | RC2 object or RC1 string | tag `1`: legacy `V6(ip, port)`; tag `2`: `V6Extended(ip, port, flowinfo, scope_id)` |

RC2 reads RC1 socket strings and legacy binary tags. RC1 cannot read RC2
objects or binary tag `2`. RC1 strings and legacy binary tag `1` omit IPv6
`flowinfo` and `scope_id`, so RC2 reads them as zero; metadata already lost by
an RC1 writer cannot be reconstructed.

## 0.3.x to 1.0 migration

The host/address taxonomy introduced in `0.3.x` remains the source-level
shape for `1.0`: `Addr` continues to distinguish `Host` and `Ipc`, and
`LocalAddr` continues to distinguish loopback from IPC. The 1.0 migration
closes the validation gap around caller-supplied host storage. Code that
constructed a domain-like `Host::Domain` value directly must now provide a
validated `Domain` through the parsing or conversion APIs. This is a source
compatibility change made to preserve the type invariant; the serialized host
variant and its wire tags remain unchanged.

---

# Design Principles

* Keep address taxonomy simple.
* Separate transport kind from locality.
* Prefer refinement types over runtime checks.
* Separate storage from semantics.
* Make every storage type generic.
* Avoid exposing platform implementation details.
* Preserve `hostaddr`'s zero-cost, generic-storage philosophy.
