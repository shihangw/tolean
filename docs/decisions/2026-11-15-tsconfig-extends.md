# Load inherited TypeScript resolution options

**Status:** accepted · **Date:** 2026-11-15

Tolean loads relative tsconfig inheritance before it checks import resolution
options. This replaces the blanket refusal of `extends` in the
[import resolution decision](2026-11-14-project-import-resolution.md).

## Decision

The native command and the WebAssembly workspace use one Lean loader. The
host supplies the file names and a function that reads their text. The
loader parses JSONC and follows `extends` without running TypeScript.

Each base contributes its compiler options independently. An array of bases
uses TypeScript 5's precedence: later bases replace earlier options, then
the child replaces each option it declares. Objects and arrays within an
option are replaced, not recursively merged. The loader tracks the current
chain, so a repeated ancestor on separate branches is not a cycle. A cycle
reports the config paths. Recursion is bounded by the workspace's file count.

An `extends` path is relative to the config that declares it. The loader
normalizes dot segments, tries the named file, then tries the name with
`.json` appended if needed. It never interprets an inherited base path
relative to the child. Missing files and paths outside the project are
errors.

The merge is a projection of TypeScript's config onto compiler options,
not a replacement for TypeScript's project builder. Tolean consumes only
`moduleResolution`. It refuses a merged `moduleSuffixes` or `rootDirs`,
because either can change which relative file wins. It does not consume
path-valued options, so it does not rebase those values to the child.
`paths` and `baseUrl` cannot enable an import: nonrelative imports remain
refused. `files`, `include`, `exclude`, `references`, output directories and
other build settings remain outside this projection. `tolean.json` selects
the sources and outputs, as before.

This boundary means no accepted path-valued compiler option can be
interpreted against the wrong config directory. A future consumer must
retain its declaring directory and implement TypeScript's path rules,
including `${configDir}`, before it can use such an option.

## Refused forms

Package names in `extends` remain unsupported. TypeScript searches
`node_modules` and can use a package's `tsconfig` field or config subpaths.
Tolean's native project enumeration excludes `node_modules`, and browser
workspaces need not contain installed packages. We refuse the name with an
explicit diagnostic rather than approximate that lookup. Absolute base
paths and bases outside the project are also refused, so both hosts see
the same inputs. Backslashes and template substitutions in `extends` paths
are refused.

These are gaps in config loading, not a claim that TypeScript refuses
those projects. Projects can copy their shared config into the workspace
and use a relative path. The merged options still face the same import
restrictions.

## Checks and trust

The import-resolution tests compare `tsc --showConfig` with the issue's
single base, a two-base chain, an array, a child override and a shared
ancestor. They also check an inherited `moduleSuffixes` and a cycle.
Project fixtures exercise the native file loader and retain their generated
Lean and manifests unchanged. Workspace tests exercise the same loader with
an in-memory reader. The existing corpus parity check covers those fixtures
when WebAssembly is built.

Config loading remains tested and trusted, like file selection. It adds
no interpreter operation, proof assumption or ECMAScript feature.
`Edition.lean` covers runtime language features, not project configuration,
so it needs no entry. Both hosts compile the same loader, and neither needs
Node or TypeScript at translation time.
