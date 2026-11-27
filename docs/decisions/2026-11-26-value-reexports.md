# Value re-exports forward the original declaration

**Status:** accepted · **Date:** 2026-11-26

A value re-export, such as `export { double } from "./origin.ts"`, makes the
re-exporting file's interface offer the declaration of `origin.ts` itself.
The re-exporting file's output adds nothing for it, and a file that imports
`double` calls `Origin.double` directly. The interpreter follows the same
path at run time: `Eval.resolveExport` models `ResolveExport` (ES2015
§15.2.1.16.3; ES2024 §16.2.1.6.3), so a call through a chain of re-exports
reaches the function of the file that declares it.

## The design question

A re-export could forward the identity of the declaration, or it could
create a new declaration in the re-exporting file, such as a Lean alias
`def double := Origin.double`.

An alias would give every re-exporting file a Lean name of its own, but the
interpreter would have to treat that name as a function too. `Eval.callIn`
looks a call up by its file and its name, and the re-exporting file declares
no function. So the proof would need a second kind of function, one that
only forwards, and every lemma about calls would have to handle it.

Forwarding needs no new kind of declaration. A function keeps its file and
its name, `FnInfo.ref`, through any number of re-exports. Type re-exports
already work this way, so a re-exported interface and a re-exported function
now behave alike. A string enum keeps its file as well, so its type is the
same in every file that names it.

## What the proof states

`program_sound` holds for programs with value re-exports. Its invariant on
the interfaces of earlier files, `Faithful`, used to say that each offered
function is exported by that very file. It now says that `resolveExport`
finds the offered function, starting at that file. A chain of re-exports can
only pass through earlier files, so as many steps as there are earlier files
resolve it. The interpreter takes one step for each file of the program.
`FaithfulE` says the same for string enums, through `Eval.exportedEnum`.

The interface of a file lists a re-exported function only when the file does
not export a function of that name itself, and takes it from the file that
`Eval.reexportSource` names. This mirrors the interpreter, so the proof does
not depend on the translator's checks for duplicate exports. The translator
still refuses a name that the file exports twice, because ECMA-262 makes it
an early error (§16.2.1.1).

## What stays refused

- `export { a as b } from "./x.ts"`. The parser refuses `as` in every import
  and export list. Renaming needs a second name in `ImportName`, and the
  parser's round-trip proof covers that structure, so it is a separate
  change. The translator side is ready for it: a renamed re-export would be
  a function whose exported name differs from `FnInfo.name`. The [renamed
  imports decision](2026-11-26-renamed-imports.md) later accepted it.
- `export * from "./x.ts"`. The parser refuses it. Its set of names depends
  on every name that the other file exports, and on the rule that a name
  from two star exports is ambiguous, which the subset does not model.
- Re-exported error classes and ordinary classes. No file can import an
  error class yet, and the elaborator lowers an ordinary class into
  declarations that do not cross files.
