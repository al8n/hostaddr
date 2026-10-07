# Security policy

## Supported versions

The latest published `0.3.x` release is the supported line for security fixes.
The `1.0.0` work in this repository is not published yet and should not be
treated as a stable release.

## Reporting a vulnerability

Please report suspected vulnerabilities privately through
[GitHub Security Advisories](https://github.com/al8n/hostaddr/security/advisories/new).
Include the affected version, a minimal reproducer, and the impact you observe.
Do not disclose a suspected memory-safety or deserialization issue publicly
until a fix or coordinated disclosure date has been agreed.

The crate's IPC wrappers are representations, not OS security checks. Callers
remain responsible for validating endpoint permissions, pathname policy, and
trust boundaries before connecting.
