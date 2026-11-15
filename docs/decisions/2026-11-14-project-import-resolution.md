# Resolve project imports before translation

**Status:** accepted · **Date:** 2026-11-14

Tolean resolves relative TypeScript imports before it translates the
program. The generated Lean and the chain manifest name the concrete files
that the resolver selected.

## Question

How should a project accept extensionless bundler imports and `.js`
imports that TypeScript resolves to `.ts`, without making the interpreter
depend on the filesystem?

## Decision

The project reads `compilerOptions.moduleResolution` from the
`tsconfig.json` next to `tolean.json`. It accepts JSON comments and trailing
commas. If that file is absent, `typescript.moduleResolution` in
`tolean.json` supplies the fallback. Per-file overrides can set that
fallback too. A present tsconfig without the setting keeps the old rule:
imports must name `.ts` files explicitly.

Under `bundler`, `./x` selects `x.ts` first, then `x/index.ts`.
Under `node16` and `nodenext`, `./x.js` selects `x.ts`. Bundler mode accepts
that substitution too. All modes accept explicit `.ts` paths. Other modes
keep the explicit-extension rule. The node modes use the ESM spelling,
even when TypeScript would allow an extensionless CommonJS import.

The resolver considers every file in the project, not just the translated
sources. If `x.ts` exists but is not listed, `./x` must not silently select
`x/index.ts`. The selected file still has to translate before the file
that imports it.

After parsing, the project replaces only the import specifiers with
concrete relative paths. It keeps the original spans. The translator and
interpreter then use their existing rule for `.ts` paths. Generated Lean
imports the selected module, and its manifest lists the resolved source
paths and their hashes, including transitive imports. Existing projects
keep their output byte for byte.

## Why

File selection belongs to the host, not to a new ECMAScript operation in
the parsed program. The IR, evaluator and interpreter need no new form,
and no new edition entry is needed. `program_sound` still applies to the
resolved program. File selection remains tested and trusted, as source
loading already is.

Both the native command and the WebAssembly build run the same pure
resolver. The project corpus checks the generated Lean and manifests.
The corpus checker also compares native workspace results with the
WebAssembly results whenever that build is available.

TypeScript 6.0.3 traces in a scratch ESM project confirmed the supported
search order. Bundler mode selected `x.ts` before `x/index.ts`, and selected
a directory's `index.ts` when there was no file. All three modes replaced
`.js` with `.ts`. Both node modes refused the extensionless ESM imports.
Explicit `.ts` imports worked with `allowImportingTsExtensions`.

## What stays refused

Tolean refuses packages, TSX, declaration files and other extensions. It
also refuses URL escapes, queries, fragments, backslashes and directory
spellings. It does not search arbitrary extensions. An unsupported file
that TypeScript would try before `index.ts` causes a refusal, not a search
for a different supported target.

A tsconfig with `extends` stays refused. Even a local `moduleResolution`
does not rule out an inherited `moduleSuffixes` setting that selects a
different file. Tolean does not load inherited configurations, so it
refuses them rather than guessing their effect. A direct `moduleSuffixes`
setting is refused too. A directory's `package.json` can redirect an
import, so that case also stays refused.

These are deliberate limits on file selection, not approximations of
TypeScript's wider resolver. Files with imports still have no certificate,
as before this decision.
