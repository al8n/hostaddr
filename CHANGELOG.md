# Unreleased

## 1.0.0-rc.2 (Target)

> This section records the release-candidate work currently being validated.

### Domain and Serde correctness

- Validate ASCII `xn--` A-labels through UTS46 on allocating domain parsers and
  verification functions, while keeping the no-alloc ASCII entry points
  structural-only.
- Decode percent-encoded input into an allocating intermediate before applying
  the final ASCII domain limit, so long Unicode input and its fully encoded
  equivalent follow the same path.
- Make `Buffer` deserialization accept borrowed, transient, and owned string
  and byte visitors used by streaming and legacy Serde deserializers.

### Portability and compatibility

- Explicitly expose the `quickcheck` feature and enable its `wasm_js` random
  backend so the all-features wasm build is supported.
- Keep the host/address taxonomy migration source-visible while preserving the
  `Addr`, `IpcAddr`, and `LocalAddr` Serde variant names and numeric tags.
- Define the cross-platform IPC and Serde compatibility range as
  `1.0.0-rc.1` through `1.0.x`: unavailable platform variants reject their
  tags, and tags are never reused.

## 1.0.0-rc.1 (2026-10-07)

> Published release candidate. The final `1.0.0` release remains subject to
> downstream validation and the compatibility checks described above.

## Soundness and correctness

- Validate `Domain`, `Host`, and `HostAddr` values during Serde deserialization
  so malformed UTF-8 and invalid domain labels cannot bypass constructors.
- Expand semantic IP classification regression coverage at every RFC boundary.

## Dependencies and portability

- Upgrade `iprfc` to the published `1.0.0` line.
- Raise the MSRV to Rust `1.89` and keep the `std` feature layered over
  `alloc`, including bare-metal no-std/no-alloc validation in CI.

## API and wire-format hardening

- Treat the host/address and IPC taxonomy as the API surface being frozen for
  `1.0.0`.
- Document that IPC wrappers do not perform OS-level validation or establish a
  trust boundary.
- Document the Serde variant names and numeric binary tags as compatibility
  contracts.
- Document that `HostAddr` conversions from `SocketAddrV6` discard `flowinfo`
  and `scope_id`.
- Keep `Eq`, `Ord`, and `Hash` representation-sensitive and case-sensitive;
  callers that need DNS-insensitive identity keys must normalize explicitly.

## Breaking changes for 1.0

- Remove the public `Buffer::push` and `fmt::Write` implementations; domain
  construction remains the validation boundary.
- Validate `Deserialize` inputs instead of allowing unchecked domain/host values.
- Parse bare IPv6 addresses before host/port splitting and standardize IDNA and
  percent-decoding validation.
- Mark extensible parsing/address enums `non_exhaustive`.
- Raise the MSRV to Rust `1.89`.

## Migration notes

The `0.3.x` host/address taxonomy is retained in `1.0`: `Addr` still
separates host and IPC transports, while `LocalAddr` still separates loopback
from IPC. Direct construction of a domain-like `Host::Domain` value is no
longer an unchecked way to bypass the `Domain` invariant; use a parsing or
conversion API to obtain the validated domain storage instead. This source
change does not alter the serialized host variant or the stable IPC/address
tags listed in the design document.

# RELEASED

## 0.3.0 (Jul 2nd, 2026)

FEATURES

- Add semantic IP and socket address wrappers for loopback, private, link-local,
  documentation, benchmark, shared, multicast, unspecified, and broadcast
  address classes.
- Add the `Addr`, `IpcAddr`, and `LocalAddr` transport taxonomy with Unix,
  Linux abstract, Windows named-pipe, and optional vsock representations.
- Add stable Serde support for host, IPC, and local-address representations.

## 0.2.4 (Apr 13th, 2026)

BUGFIXES

- Fix domain validation accepting names longer than 253 bytes (RFC 1035 violation)
- Fix `HostAddr` `Display` for IPv6 with port producing ambiguous output (`::1:8080` instead of `[::1]:8080`)
- Remove misleading `unsafe` from internal `Domain` constructors that cannot cause memory unsafety

## 0.1.2 & 0.1.3 (Apr 9th, 2025)

FEATURES

- Support `no-alloc` environment for ASCII only domain and hosts.
- Add `verify_domain`, `verify_ascii_domain` and
  `verify_ascii_domain_allow_percent_encoding`.
- Add `as_str` and `as_bytes`

## 0.1.0 (Mar 24th, 2025)

FEATURES

- `Host`, `HostAddr`, `Domain` implementation
