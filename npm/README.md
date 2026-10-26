# tolean (npm)

The npm build of [tolean](../README.md). It has:

- the `tolean` command: `tolean <input.ts> <output.lean> <Lean.Namespace>`,
  which translates one TypeScript file in the tolean subset to Lean;
- `translateSource` and `TranslateError`, for the same from code;
- `lean/`: the Lake package that generated code imports (the TypeScript
  spec and `#audit_claims`).

Licensed under the Apache License 2.0 (`LICENSE`).

The translator here still reads TypeScript with `tsc`. It is the next part to
move to Lean, after the parser.
