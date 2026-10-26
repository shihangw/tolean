# Plan: effects and trust boundaries in the translator core

**Status:** planned, not built · **Date:** 2026-10-25

Real code calls libraries that change the world outside the program. A
logger writes lines, a tracer sends spans, and a database client changes
rows. Tolean refuses such calls today, except for two narrow cases. The Go
translator erases observability statements, and a Go interface becomes a
store whose model a proof plugs in. This plan replaces both cases with one
mechanism that the TypeScript and Go translators share. The mechanism also
covers SQL later.

The mechanism has one purpose: it fixes a trust boundary. A trust boundary is
a small contract at the point where translated code calls a library. Proofs
about the application assume the contract. A separate proof, which can come
later, shows that the library keeps it. The two sides are verified
independently, so application proofs can finish now and stay valid when the
library proof lands.

## 1. Effect declarations

A library describes its effects in a declaration file, written in the
library's own language. This works like a TypeScript `.d.ts` file: people
write it once, publish it, and reuse it in every project. In TypeScript, a
JSDoc tag marks each function:

```ts
declare module 'tracer' {
  interface Tracer {
    /** @effect observe  @callback once */
    trace<T>(name: string, fn: () => T): T;
  }
}
```

In Go, a stub file carries directives:

```go
//tolean:effect observe; returns-context
func StartSpan(ctx context.Context, op string) (Span, context.Context)
```

User code needs no tags. The translator infers the effects of each function
from the functions it calls. A team may add `@effect pure` to a function, and
then the translator refuses any later change that makes the function call an
effectful one.

## 2. The tags

The tag set is small and fixed, so the boundary stays stable while libraries
grow. Tolean proves the law of each tag once, in its own library.

| Tag | Meaning | Law that Tolean proves once |
|---|---|---|
| `pure` | The function has no effect. | It is an ordinary function. |
| `observe` | The call only writes telemetry. | No result depends on the telemetry, so a proof about values can drop it. |
| `reads R`, `writes R` | The call reads or writes the resource `R`, such as a store or a table. | Code that does not write `R` leaves `R` unchanged. |
| `fails` | The call can return an error or throw. | The error is an explicit result. |
| `returns-context` | The call returns a context. | The context is opaque, so the old and the new context behave the same. |
| `callback once` | The call runs its callback once, at once, and returns its result. | The call equals the body of the callback. |

## 3. The shared core

The new module `tolean/Effects/` holds everything that does not depend on a
language. Each translator keeps only the part that reads its own syntax.

| Part | Where | What it does |
|---|---|---|
| Tags and laws | `tolean/Effects/Tags.lean` | It defines one type class per tag, such as `Observe m` and `Reads R m`, and it proves each law. |
| Declarations | `tolean/Effects/Decl.lean` | It holds a library's declarations as data: the function, its tags, the library version, and the SHA-256 of the declaration file. |
| Inference | `tolean/Effects/Infer.lean` | It computes the effects of each function from the call graph, as the union over its callees. It refuses a call that has neither a translation nor a declaration. |
| Seam rules | `tolean/Effects/Check.lean` | It checks how code uses each call. Section 4 lists the rules. |
| Lean output | `tolean/Effects/Emit.lean` | It writes the class constraints of each function, such as `[Monad m] [Observe m]`, and the lemmas of section 5. |
| Readers | `tolean/TypeScript/EffectDecl.lean`, `tolean/Go/EffectDecl.lean` | Each reads JSDoc tags or `//tolean:` directives into the shared data. |

The Go translator moves from one fixed `StateM State` to these classes. The
store interface becomes a declared resource, and today's erasure becomes the
`observe` tag. The TypeScript translator gains effectful functions. A
function that calls an effect becomes Lean `do` code, and a pure function
stays a plain term, as it is now.

## 4. Seam rules

The translator checks these rules at every call. They make sure that
application code relies only on what a contract states.

1. A call that has neither a translation nor a declaration is refused. The
   translator never assumes that an unknown call is pure.
2. Code may not use the result of an `observe` call. The one exception is a
   method chain on the same object.
3. The arguments of an effect call must have no side effects.
4. A resource that only has `observe` operations has no reads.
5. Code may not read a context that came from a `returns-context` call.

## 5. Generated lemmas

For each function, the translator writes lemmas that follow from its effect
constraints. A fixed tactic proves them, so the Lean kernel checks them, and
nobody reviews them. A footprint lemma states that a function without
`writes R` leaves `R` unchanged. A telemetry lemma states that the function
gives the same result when its telemetry is dropped. Then a proof about
values removes telemetry with one rewrite.

## 6. The chain

Each declaration file is a node in the chain manifest. The node has the tags'
status, the library version, and the hash of the file. `chain check` fails
when the declaration file or the locked library version changes, because the
boundary is then open again. `chain trust` lists each open boundary that a
claim crosses.

A boundary moves through three stages:

| Stage | What supports the tags | Status |
|---|---|---|
| Declared | A person wrote the declaration. | `trusted` |
| Tested | The library ran under instrumentation. For example, a check removed every `observe` call and saw no change in any result. | `tested` |
| Proved | Tolean translated the library and proved that it keeps its tags. | `proved` |

The proofs stop at a small set of primitive effects, such as system calls,
the clock and the network. These primitives stay trusted, as the JavaScript
engine and the Go compiler are trusted now, and every program shares them.

## 7. Value claims are partial

A proof about values says that a result is right if the function returns. It
does not say that the function returns, or that it returns in time, because
a logger can block and a call can panic. Whether a call can fail is part of
its declaration, so the assumption that a call never fails stays visible.

## 8. Steps

Each step ends with all checks green and with no change to the output of
code that has no effects.

1. Add `Tags.lean` with the type classes and their laws, together with the
   theorem that dropping `Observe` does not change a result.
2. Add `Decl.lean` and the Go reader. Then move the Go translator to the
   class constraints, and turn the ledger's store and its erased logging into
   declarations. The ledger proofs must still pass.
3. Add `Infer.lean` and `Check.lean`, and use them in the Go translator. Add a
   corpus of refused cases, one for each seam rule.
4. Add `Emit.lean` for the generated footprint and telemetry lemmas.
5. Add the TypeScript reader and effectful functions in both TypeScript
   translators, so that the two translators still give the same output.
6. Add declaration nodes, version pins and hashes to the chain manifest and to
   `chain check`.
7. Write the first shared declaration file, for a tracing library, and add a
   check that tests the library under instrumentation.

## Open questions

- Should a declaration file live with Tolean, in a shared registry like
  DefinitelyTyped, or with each project?
- Should SQL statements become a declared resource, so that SQL uses the same
  classes as Go and TypeScript?
- How should the instrumented test in stage 2 run for libraries that call
  the network?
