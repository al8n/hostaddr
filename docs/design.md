# Address Abstraction Design (v2)

> Status: the core taxonomy below is implemented in the current `0.3.x` line.
> The `1.0.0` release is not published yet; this document records the API and
> wire-format contract being stabilized for that release.

## Goals

This design extends `hostaddr` from Internet host addresses to a complete, type-safe address abstraction for Rust.

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

`Addr` represents every address accepted by a runtime.

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

Storage type for the optional filesystem view:

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

Every address owns only its semantic validation.

Storage is entirely user selectable.

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

The address types never dictate allocation strategy.

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
planned `1.0.0` compatibility contract. Deserialization must continue to
validate domain and semantic-address invariants rather than constructing
unchecked values.

---

# Design Principles

* Keep address taxonomy simple.
* Separate transport kind from locality.
* Prefer refinement types over runtime checks.
* Separate storage from semantics.
* Make every storage type generic.
* Avoid exposing platform implementation details.
* Preserve `hostaddr`'s zero-cost, generic-storage philosophy.
