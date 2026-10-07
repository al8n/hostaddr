# Security policy

## Supported versions

The latest stable release is the published `0.3.x` line. The latest published
pre-release is `1.0.0-rc.2` (2026-10-08); it should not be treated as stable.
Security reports are nevertheless welcome for both lines so fixes can be
carried into the final `1.0.0` release.

## Reporting a vulnerability

Please report suspected vulnerabilities privately through
[GitHub Security Advisories](https://github.com/al8n/hostaddr/security/advisories/new).
Include the affected version, a minimal reproducer, and the impact you observe.
Do not disclose a suspected memory-safety or deserialization issue publicly
until a fix or coordinated disclosure date has been agreed.

The crate's IPC wrappers are representations, not OS security checks. Callers
remain responsible for validating endpoint permissions, pathname policy, and
trust boundaries before connecting.
