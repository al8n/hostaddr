# Unreleased

## 1.0.0-rc.1 (Unreleased)

> This section describes work in progress for the not-yet-published `1.0.0`
> release. It is not a release announcement.

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
- Add `verify_domain`, `verify_ascii_domain` and `verify_ascii_domain_allow_percent_encode`.
- Add `as_str` and `as_bytes`

## 0.1.0 (Mar 24th, 2025)

FEATURES

- `Host`, `HostAddr`, `Domain` implementation
