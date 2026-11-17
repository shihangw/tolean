# Record shared TypeScript configs as project inputs

**Status:** accepted · **Date:** 2026-11-17

This supersedes the project boundary for relative bases in the
[inheritance decision](2026-11-15-tsconfig-extends.md). That boundary broke
monorepo packages in 0.3.1, even when their source files had no imports.

## Decision

A relative `extends` path may name a config outside the directory that
contains `tolean.json`. The native host reads the reachable config chain
before translation. A workspace host supplies those same files as text,
with paths relative to the project root, including leading `../` segments.
The shared loader resolves and merges that snapshot in both builds.

Each TypeScript manifest records the config paths and SHA-256 hashes among
its source inputs. The workspace result reports the same references in
`configInputs`. Thus a shared base is an explicit input, not an ambient
dependency that only the native build can see. A browser cannot read a
parent directory on its own: its host must supply every inherited config.
A missing base is an error.

Only config paths can cross this boundary. External workspace files do not
enter source selection or import resolution. Imports still use the existing
project-bounded path resolver. Package and absolute bases remain unsupported,
as do backslashes and template substitutions. The previous merge rules and
checks on compiler options remain unchanged.

The host bounds config discovery at 1024 levels and reports cycles with
their paths. The loader then merges the collected files with its existing
cache and file-count bound. Neither stage runs TypeScript.

## Checks and trust

The monorepo fixture reproduces issue #260 without imports. Its project root
is below the fixture root, so the native loader reads a real parent config.
The workspace check supplies the same relative paths and compares the full
native and WebAssembly results. It also compares the reported config hashes
with the native manifest.

Config discovery and hashing remain tested and trusted. They add no proof
assumption or interpreter operation.
