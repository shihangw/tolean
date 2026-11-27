# Renamed imports and exports keep the declaration's name

**Status:** accepted · **Date:** 2026-11-26

`import { a as b }`, `export { a as b } from "./x.ts"` and a local
`export { a as b }` translate. A function or a string enum known under
another name keeps the reference to its declaration, so the output calls
`X.a` wherever the source calls `b`. The interpreter resolves the same names
the same way: `Eval.resolve` looks up the import that binds `b` and asks the
other file for its export `a`. `Eval.resolveExport` models `ResolveExport`
(ES2015 §15.2.1.16.3; ES2024 §16.2.1.6.3). It follows a renamed re-export to
the name before `as`, and finds a local `export { a as b }` as the function
`a` of the file.

## The parser

`ImportName` has a second name, `alias`, which is `none` without `as`, and
`ImportName.binding` is the name that the file binds or exports. The printer
writes `a as b`, and the parser's round-trip proof covers the new words:
`importTail_ok` reads the alias back, and `importTail_wf` keeps the
well-formedness invariant. One form cannot round-trip. `type as x` reads as
the name `as` marked with `type`, so the parser refuses a renamed `type`
without `type` before it. The parser never gives that tree anyway, and
`ImportName.ok` states the rule.

## The design question

A renamed name could become a new declaration, a Lean alias
`def b := X.a`, or it could keep the identity of `a`.

The [value re-exports decision](2026-11-26-value-reexports.md) chose to
forward the identity for re-exports, and renames follow it. `FnInfo` and
`EnumInfo` get `declName`, the name that the declaring file uses, so
`FnInfo.ref` stays the declaration's reference under any name, and
`FnInfo.rename` changes only the name that code calls. A renamed string
enum is the same Lean type in every file, so values pass between files
that name it differently.

## What the proof states

`program_sound` holds for programs with renames. `declRefs` now pairs the
name that a declaration binds with the reference that it adds, so
`module_resolves` connects a call of `b` to the export `a` that the other
file's interface offers. The interface's own functions come from
`Eval.exportedFunction`, the interpreter's rule for what a file exports
under a name, so the `Faithful` invariant follows from the spec and not
from the translator's duplicate checks. Two names of one import may not be
equal (`boundNames` is free of duplicates), which picks the import entry
that `Eval.resolve` finds.

## What stays refused

- Renaming a type: `import { type A as B }` and
  `export { type A as B } from "./x.ts"`. The output names a type by its
  declaration, so a second name would need a Lean abbreviation in the
  importing file, and the interface tables match types by name.
- Renaming anything but a function in a local export list. A string enum
  exports only with `export enum`, and a type is not renamed.
- A string literal as a name, `export { a as "b" }` (ES2022). The parser
  reads only identifiers.
- `export * from "./x.ts"`, re-exported error classes and ordinary classes,
  for the reasons in the value re-exports decision.
