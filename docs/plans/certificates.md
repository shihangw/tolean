# Plan: certificates and round-trip proofs

**Status:** phases 1 to 3 built, phase 4 step 1 built, phase 6 steps 1 to 3 built · **Date:** 2026-10-27

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
   2. **Round trips.** With a total printer from syntax trees back to source
      text, Tolean proves the round trip `parse (print t) = .ok t` for every
      tree in the subset.
5. **The interpreter against Node.** A differential test runs random programs
   in the interpreter and in Node, and requires the same results. This is
   evidence that the interpreter means what JavaScript means.
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
   4. **The printer link.** For each file, a theorem states that the printed
      definitions compute what the evaluator gives for the tree. Each output
      form has one lemma, so the proof follows the tree and does not search.
      The kernel checks `translate program = .ok out` for the file, so with
      step 3 the whole file is proved. Every certificate then follows from
      one theorem.

## Why a certificate first

A proof for all programs needs the same interpreter as a certificate, and it
is much harder to write. A certificate gives the same guarantee for each file
that it covers, and it gives it now. The generator is not trusted, because
Lean checks every theorem it writes, so the generator can be simple.
