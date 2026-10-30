# Tolean and Aeneas

[Aeneas](https://github.com/AeneasVerif/aeneas) translates safe Rust into
pure Lean, and Tolean took its central idea from it. Both tools write the
source as readable Lean functions, and a person proves claims about those
functions. The two differ in where the purity of the output comes from, and
in how much of the translation is itself proved.

This page describes Aeneas as its papers and repository present it. Aeneas
changes quickly, so check its repository before you rely on a detail here.

## The two pipelines

```
Aeneas:  Rust ──rustc + Charon──▶ LLBC ──Aeneas (OCaml)──▶ Lean functions in a Result monad
Tolean:  TypeScript ──Tolean parser (Lean)──▶ syntax tree ──translator (Lean)──▶ output tree ──printer──▶ plain Lean functions
```

Charon reads a crate through `rustc` and writes it as LLBC, the low-level
borrow calculus. LLBC is a small language that keeps Rust's borrows explicit.
Aeneas then runs LLBC symbolically and writes Lean, and it can also write
F*, Rocq and HOL4.

Tolean does every step in Lean. Its parser reads the TypeScript source, and
its translator builds the output as a syntax tree. A printer then writes that
tree as Lean text.

## Side by side

| | Aeneas | Tolean (TypeScript) |
|---|---|---|
| Source | Safe Rust | A pure subset of TypeScript |
| Front end | `rustc`, which also type-checks and borrow-checks, and Charon | Tolean's parser and type checker, written in Lean and tested against `tsc` |
| Where the translator runs | OCaml | Lean |
| Proof of the translator | The ICFP 2024 paper proves on paper that the symbolic semantics of LLBC is sound. The OCaml code that implements it is trusted. | `program_sound` proves the translator in Lean for every program it accepts, up to the printer |
| Proof for one file | None | A [certificate](typescript/README.md#certificates) that the kernel checks. It proves the parse, the translation and the printer link for that file. |
| Meaning of the source | The semantics of LLBC, as the papers define it | An interpreter in Lean, `tolean/TypeScript/Spec/Eval.lean`, which runs and is tested against Node |
| Shape of the output | Every function returns a `Result`: `ok`, `fail` for a panic or an overflow, and `div` for a loop that does not end | Plain functions, because the subset has no effects |
| Integers | Machine types such as `U32` and `Usize`. Overflow gives `fail`. | `bigint` becomes `Int`. `number` becomes an abstract `JSNumber N`, whose laws are tested against Node. |
| Mutation | A `&mut` argument becomes a forward function and a backward function. The backward function gives the new value of what was borrowed. | Only locals that the function owns can change, so a mutation becomes a new value |
| What runs | The binary that `rustc` builds | The JavaScript that type stripping gives, on a JS engine |
| Other backends | F*, Rocq and HOL4 | Lean only |

## Where the purity comes from

Aeneas writes pure functions because Rust's borrow checker rules out
aliasing. When no two names can reach the same value, a mutation in place
has the same effect as a pure update of that value. `rustc` checks this for
every program, so Aeneas gets it for free.

TypeScript has no borrow checker, and objects alias freely. Tolean gets the
same property from its subset instead: a function can change only the locals
it owns, and it can read an owned array only in its return value. This is
the idea that Tolean takes from Aeneas, and the
[Prior work](../README.md#prior-work) section says so.

The cost appears when Tolean allows more. Once the subset lets code change a
shared object, the generated Lean needs a heap, and Aeneas never needs one.
The [shared core plan](plans/shared-core.md) describes that step.

## Where Tolean proves more

- **The translator.** Tolean proves its translator in Lean, and the kernel
  checks that proof. Aeneas proves the soundness of its method on paper, and
  its implementation is trusted.
- **One file at a time.** A certificate proves, for every input, that a
  JavaScript interpreter in Lean and the generated Lean function give the
  same result. Aeneas has nothing that the kernel checks per file.
- **The front end runs in the kernel.** A certificate makes the kernel run
  Tolean's parser on the file's characters, so a certified file does not
  trust the compiled `tolean` binary. Aeneas trusts `rustc` and Charon.

## Where Aeneas is ahead

- **Mutation.** The backward functions let Aeneas translate code that
  changes values through `&mut` borrows. Tolean refuses any change to a value
  that the function does not own.
- **Coverage of the language.** Aeneas handles a large part of safe Rust,
  with structures, enumerations, generics and traits, and people have used
  it on real code. Tolean's subset is smaller.
- **Failure and divergence.** Every Aeneas function can fail or diverge, and
  the `Result` monad makes that explicit. Tolean's output has no monad yet,
  so its subset refuses code that could throw.
- **Its semantics is published.** The papers define LLBC and prove its
  symbolic semantics sound. Tolean's interpreter follows ECMA-262, but it is
  tested against Node rather than proved against a formal semantics of
  JavaScript.

## What both trust

- The compiler or engine that runs the code: `rustc` for Aeneas, and the
  JavaScript engine and type stripping for Tolean.
- That callers meet each theorem's preconditions. Neither tool checks this
  where unverified code calls verified code.
- The Lean kernel and Lean's axioms.

## What Tolean can reuse

The `Result` monad of Aeneas, with `ok`, `fail` and `div`, is the kind of
shared piece that the [shared core plan](plans/shared-core.md) describes.
Effectful TypeScript needs about the same piece for `throw` and for loops
that may not end, and Go needs it for `panic`. How Tolean writes a loop that
may not end, with fuel as now or with a `div` result as Aeneas does, is an
open question in that plan.

## Sources

- Son Ho and Jonathan Protzenko. *Aeneas: Rust verification by functional
  translation.* ICFP 2022.
- Son Ho, Aymeric Fromherz and Jonathan Protzenko. *Sound borrow-checking for
  Rust via symbolic semantics.* ICFP 2024.
- [Aeneas](https://github.com/AeneasVerif/aeneas) and
  [Charon](https://github.com/AeneasVerif/charon) on GitHub.
