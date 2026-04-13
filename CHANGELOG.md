# RELEASED

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
