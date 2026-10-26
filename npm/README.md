# Tolean (npm)

The npm build of [Tolean](../README.md). It has:

- the `tolean` command: `tolean [--target ES20xx] <input.ts> <output.lean> <Lean.Namespace>`,
  which translates one TypeScript file in the Tolean subset to Lean;
- `translateSource`, for the same from code, and `translateWorkspace`, which
  translates every unit that a `tolean.json` names, in TypeScript, Go or SQL;
- `lean/`: the Lake package that generated code imports (the language specs
  and `#audit_claims`).

The translator is Tolean's own, written in Lean and compiled to WebAssembly
by `wasm/build.sh`, so it writes the same Lean as the `tolean` command that
Lake builds, on any platform that runs Node 22 or later. `pnpm build` copies
it from `wasm/out/`, so build it first.

Licensed under the Apache License 2.0 (`LICENSE`).
