# Tolean (npm)

The npm build of [Tolean](../README.md). It has:

- the `tolean` command, with the same commands as the one that Lake builds,
  such as `tolean translate` with a `tolean.json`;
- `translateSource`, which translates one TypeScript file, and
  `translateWorkspace`, which translates every unit that a `tolean.json`
  names, in TypeScript, Go or SQL;
- `lean/`: the Lake package that generated code imports (the language specs
  and `#audit_claims`).

Both run the native `tolean` binary. It comes from the package for the
platform, such as `@tolean/darwin-arm64`, for each platform that Lean
supports: macOS and Linux on arm64 and x64, and Windows on x64. Until those
packages are published, set `TOLEAN_BINARY` to a `tolean` that Lake built.

Licensed under the Apache License 2.0 (`LICENSE`).
