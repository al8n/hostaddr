# Security policy

## Supported versions

The latest stable release line is `0.3.x`. Security reports are welcome for
the supported `0.3.x` line. `1.0.0-rc.3` is an unpublished prerelease and is
not a stable support promise; reports for it are still welcome during RC
validation.

## Reporting a vulnerability

Please report suspected vulnerabilities privately through
[GitHub Security Advisories](https://github.com/al8n/hostaddr/security/advisories/new).
Include the affected version, a minimal reproducer, and the impact you observe.
Do not disclose a suspected memory-safety or deserialization issue publicly
until a fix or coordinated disclosure date has been agreed.

The crate's IPC wrappers are representations, not OS security checks. Callers
remain responsible for validating endpoint permissions, pathname policy, and
trust boundaries before connecting.
