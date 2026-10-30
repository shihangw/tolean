# Plan: certificates and round-trip proofs

**Status:** phases 1 to 6 built · **Date:** 2026-10-29

A certificate proves the translation of one file. It states, for each
function, that an interpreter of the source language and the translated Lean
give the same result for every input. When the certificate compiles, that
file no longer trusts the translator. This plan lists the phases that take
certificates from the first small subset to the whole TypeScript subset, and
then to a parser whose own correctness Lean can check.

## What a certified file trusts

A certified file trusts two links instead of the translator:

| Link | Why it is trusted | How it stops being trusted |
|---|---|---|
| The parser | It turns the source text into the syntax tree that the certificate is about. The kernel checks that it gives that tree for the file, but not that it reads TypeScript correctly. | Round-trip proofs and a grammar check the parser itself (phase 4). |
| The interpreter | It defines what the subset means. | It stays a specification. Phase 5 tests it against Node on random programs, and later it can come from a formal semantics of ECMA-262. |

The printer that writes the syntax tree as a Lean term was trusted too. Now
each certificate proves `parseChars sourceChars = .ok program`, so a wrong
printer gives a certificate that Lean refuses.

## Phases

1. **Loop-free functions (built).** The interpreter covers `const` and
   `let`, assignment, `if`, `return`, blocks, calls, objects, arrays,
   `bigint`, `boolean`, `string` and `T | null`. `tolean certify` writes the
   theorems, and the tactic `certify_tac` proves them. Six corpus files and the
   gauge example have certificates, and CI checks them.
2. **Loops (built).** The interpreter gains `for … of` and `push` onto an
   owned array. Tolean proves one general lemma, `execLoop_foldl`: when one
   run of the loop body and one step of the fold agree, the loop and
   `List.foldl` agree. Each certificate states a lemma for each loop, for
   every environment whose variables have values of the right types, and
   proves it from the general one. The theorem of the function then uses
   that lemma as a rewrite rule. The RBAC example now has a certificate.
3. **Numbers (built).** The interpreter takes its `number` values from the
   same abstract model, `JSNumber N`, that the translation uses. So each
   certificate holds for every `N`, and it does not assume the number laws.
   A certificate proves each number literal's value with `decide`, because
   `simp` cannot run the literal parser. Every accepted corpus file now has
   a certificate.
4. **A total parser.**
   1. **The kernel runs the parser (built).** The lexer and the parser are
      total, with fuel. They read their input from the front of a list,
      because the kernel reads an `Array` and the bytes of a `String` from
      the start each time, which made lexing quadratic. A certificate holds
      the source one line at a time, as `chars!"…"`. The macro reads each
      string literal as its characters when Lean elaborates the file, so the
      certificate reads as the source, and the kernel never decodes a
      `String`. The kernel takes quadratic time to reduce `String.toList` on
      a literal ([lean4#16012](https://github.com/leanprover/lean4/issues/16012)).
      The certificate proves
      `parseChars sourceChars = .ok program` with `decide +kernel`. Lean
      cannot derive `DecidableEq` for a syntax tree, so
      `Syntax/Equality.lean` gives `Module.beq` and proves that it decides
      equality. This removes the term printer from the trusted links. The
      kernel parses a 2.7 KB file in about ten seconds.
   2. **Round trips (built).** Tolean proves that the parser reads its own
      printed source back. `parseChars_reads` in `Syntax/RoundTripText.lean`
      states it: when the parser gives a module from some characters, it
      reads the printed source of that module as the same module, apart from
      spans. The theorem has no hypothesis other than the parser's result.

      The printer is `Syntax/Source.lean`. It writes each node in one form,
      every statement on a line of its own and ending in `;`, and every two
      tokens one space apart. A statement breaks across lines in one place
      only, between the name `async` and the `(` of a call of it. ECMA-262
      reads `async (1)` on one line as a call, but `tsc` can read it as the
      start of an async arrow function. ECMA-262 lets no line break come
      between `async` and the parameters of an async arrow function, and
      `tsc` reads none after one. So with the line break, both read a call.

      The proof has these parts. Each compares trees apart from spans, and
      a well-formed tree is one that has the shape that the parser reads.

      | What it states | Theorem | File |
      |---|---|---|
      | The parser reads the printed tokens of every well-formed type as that type, given fuel for how deep the type nests. | `types_reads` | `Syntax/RoundTrip.lean` |
      | The same for each level of the expression parser, when the target edition has the operators that the expression uses. | `exprs_read` | `Syntax/RoundTripExpr.lean` |
      | The same for statements, in a function or not and in a loop or not. | `stmts_read` | `Syntax/RoundTripStmt.lean` |
      | `parseModule` reads the tokens of the printed lines of every well-formed module, which the end of the file follows, as that module. | `module_reads` | `Syntax/RoundTripDecl.lean` |
      | Every module that the parser gives is well formed, and each word that it prints is one that the lexer reads back. | `parseTokens_wf` | `Syntax/ParseWF.lean` |
      | The lexer reads the printed source as the tokens of the printed lines, with the line breaks that `Laid` states. | `lexChars_render` | `Syntax/RoundTripLex.lean` |
      | The printer puts a line break inside a line only before a `(`. | `Module.breaksOK` | `Syntax/RoundTripText.lean` |

      `tolean parse --round-trip` prints the tree as source, parses that,
      and requires the same tree apart from spans.
      `tests/typescript/check.ts` runs it on every tree that the parser
      gives, on the corpus and on random programs. The proof is about the
      Lean definitions, and the test checks the compiled binary.
5. **The interpreter against Node (built).** `tests/typescript/interpreter.test.ts`
   runs random programs of the subset with random arguments in the interpreter
   and in Node, and requires the same results. This is evidence that the
   interpreter means what JavaScript means. `tolean interpret` runs the
   interpreter with Lean's `Float` as the number model, because a `Float` is
   an IEEE 754 double, as a JS `number` is. The test compares numbers by their
   64 bits, so it tells `-0` from `0`. When the interpreter gives a value, Node
   must return the same value. When the translator accepts the program and
   the interpreter gives no value, Node must throw. When Node does not load a
   program, because it breaks an early error rule such as a name declared
   twice, the translator must refuse it. `nix run .#test-engines` runs the
   test on every maintained Node release line, with 1,000 programs from a new
   seed each time.
6. **The translator for all programs.** Tolean proves one theorem about the
   translator, instead of one certificate per file. The theorem covers every
   program that the translator accepts. The phase has four steps.
   1. **The output as a syntax tree (built).** The translator builds the
      Lean code as a tree (`tolean/TypeScript/Output.lean`), and a printer
      writes the tree as text. The text is the same as before, byte for
      byte. So a theorem can now state what the translator writes.
   2. **A total translator (built).** The translator and the analyses it
      uses are total functions, so Lean can reason about them and the kernel
      can run them. The analyses recurse on the syntax tree. The translator
      takes fuel: each call uses one unit, and the translation starts with
      four units per character of the source. A program nests at most a few
      calls deep per character, so the fuel never runs out on a real file.
      If it did run out, the translator would refuse the file, and the
      theorem is only about files that the translator accepts.
   3. **The meaning of the output (built).** `Output/Eval.lean` gives each
      tree a meaning, over the same values as the interpreter. Tolean proves
      `translate_sound` in `Proof/Module.lean`: when the translator accepts a
      file, a function of the output gives a value only when the interpreter
      gives the same value for the same call. The theorem holds for every
      input, every model of numbers and every amount of fuel. It does not
      need the translator's types to be right, because it follows the
      evaluation of the output back to the source. The proof is in three
      files. `Proof/Expr.lean` covers expressions, `Proof/Stmt.lean` covers
      statements, and `Proof/Module.lean` covers calls by induction on the
      fuel. `program_sound` covers a program of several files, whose files
      import functions and interfaces from each other. While writing it, we
      found two interpreter rules that did not
      follow ECMA-262, shorthand properties and `-Infinity` under a local
      `Infinity`, and we fixed them. We also found a test against `null`
      whose answer the type fixes. The output dropped its operand, so the
      subset now refuses that test.
   4. **The printer link (built).** A certificate holds the output tree as a
      Lean term, and the kernel checks with `translatesTo` that the
      translator gives that tree for the parsed program. For each function,
      a `link` theorem states that the printed definition computes what the
      evaluator gives for the tree, and `link_tac` proves it by unfolding
      the evaluator. A loop's lemma follows from `runFold_foldl`. With step
      3, `decls_sound` turns the link into the certificate's theorem, so
      every certificate now follows from one theorem and none unfolds the
      interpreter. All 29 accepted corpus files have such a certificate.
      Two changes made this possible. `alwaysReturns` became structural, so
      the kernel can run the translator on an `if`. And `let (x, y) := …`
      in the evaluator gives `x` and `y` their new values in place, as every
      lookup sees it, so a loop leaves the environment the same length.

## Why a certificate first

A proof for all programs needs the same interpreter as a certificate, and it
is much harder to write. A certificate gives the same guarantee for each file
that it covers, and it gives it now. The generator is not trusted, because
Lean checks every theorem it writes, so the generator can be simple.
