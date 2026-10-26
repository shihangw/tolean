# Plan: certificates and round-trip proofs

**Status:** phase 1 built · **Date:** 2026-10-26

A certificate proves the translation of one file. It states, for each
function, that an interpreter of the source language and the translated Lean
give the same result for every input. When the certificate compiles, that
file no longer trusts the translator. This plan lists the phases that take
certificates from the first small subset to the whole TypeScript subset, and
then to a parser whose own correctness Lean can check.

## What a certified file trusts

A certified file trusts three links instead of the translator:

| Link | Why it is trusted | How it stops being trusted |
|---|---|---|
| The parser | It turns the source text into the syntax tree that the certificate is about. | Phase 4 makes the parser total, so that the kernel checks `parse source = program` for each file. Round-trip proofs and a grammar then check the parser itself. |
| The term printer | It writes the syntax tree as a Lean term. | Phase 4 removes it, because the kernel compares the parser's output with the term directly. |
| The interpreter | It defines what the subset means. | It stays a specification. Phase 5 tests it against Node on random programs, and later it can come from a formal semantics of ECMA-262. |

## Phases

1. **Loop-free functions (built).** The interpreter covers `const` and
   `let`, assignment, `if`, `return`, blocks, calls, objects, arrays,
   `bigint`, `boolean`, `string` and `T | null`. `tolean certify` writes the
   theorems, and the tactic `certify_tac` proves them. Six corpus files and the
   gauge example have certificates, and CI checks them.
2. **Loops.** The interpreter gains `for … of`. tolean proves one general
   lemma: when the loop body and the fold step agree on every element, the
   loop and `List.foldl` agree. Each certificate then applies the lemma with
   an induction over the list. The RBAC example becomes certifiable.
3. **Numbers.** The interpreter gains `number` values through the same
   abstract number model that the translation uses, so a certificate holds for
   every model that keeps the number laws.
4. **A total parser.** The lexer and the parser become total functions, with
   fuel or with recursion that Lean accepts. Then the kernel can run them, and
   each certificate checks `parse source = .ok program` by `rfl`. This removes
   the term printer from the trusted links. With a total printer from syntax
   trees back to source text, tolean proves the round trip
   `parse (print t) = .ok t` for every tree in the subset.
5. **The interpreter against Node.** A differential test runs random programs
   in the interpreter and in Node, and requires the same results. This is
   evidence that the interpreter means what JavaScript means.
6. **The translator for all programs.** With the interpreter and a total
   parser in place, tolean proves `run program f args = translate program f args`
   for every program the translator accepts. Every certificate then follows
   from one theorem.

## Why a certificate first

A proof for all programs needs the same interpreter as a certificate, and it
is much harder to write. A certificate gives the same guarantee for each file
that it covers, and it gives it now. The generator is not trusted, because
Lean checks every theorem it writes, so the generator can be simple.
