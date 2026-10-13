# Security policy

## Supported versions

The latest stable release line is `1.0.x`. Security reports are welcome for
the supported `1.0.x` line and the previous `0.3.x` line so fixes can be
carried into maintained releases.

## Reporting a vulnerability

Please report suspected vulnerabilities privately through
[GitHub Security Advisories](https://github.com/al8n/hostaddr/security/advisories/new).
Include the affected version, a minimal reproducer, and the impact you observe.
Do not disclose a suspected memory-safety or deserialization issue publicly
until a fix or coordinated disclosure date has been agreed.

The crate's IPC wrappers are representations, not OS security checks. Callers
remain responsible for validating endpoint permissions, pathname policy, and
trust boundaries before connecting.
