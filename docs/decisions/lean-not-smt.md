# Why tolean writes Lean instead of SMT queries

**Status:** accepted · **Date:** 2026-10-25

tolean turns TypeScript into Lean 4 definitions, and we write and check
proofs about a program in Lean. Before we built the translator, we
considered a different design. In that design, the translator would turn the
same TypeScript subset straight into queries for an SMT solver such as Z3,
and the solver would prove the specs automatically. Verus works this way for
Rust, and Dafny works this way for its own language. This note explains why
we chose Lean, what the choice costs us, and where Z3 still helps.

## 1. The two designs

In the SMT design, the specs live in the TypeScript itself. A programmer
writes calls such as `requires`, `ensures` and `invariant`, which do nothing
when the program runs. The translator reads each function together with its
specs and builds one formula for it. Then it asks Z3 whether any input breaks
the spec. If Z3 finds none, the function meets its spec for every input.
Simple code needs no proof at all in this design. For example, Z3 can prove a
bounded counter update over `bigint` values in milliseconds, as long as
someone has written down the loop invariants.

In the Lean design, which we chose, the translator writes Lean definitions
that a person can read. Those definitions import a model of JavaScript values
that we trust. A proof is an ordinary Lean theorem about the definitions.
Lean's tactics, such as `simp`, `omega` and `grind`, often close a goal in one
line. But someone still has to ask for each proof, and Lean's kernel checks
every step of it.

Both designs read the same subset of TypeScript, and both refuse the same
code. The difference is in who finds the proof and who checks it.

## 2. Why we did not choose SMT

Our first reason is that an answer from a solver does not stay fixed. Z3 can
decide some kinds of logic completely, such as linear arithmetic on integers.
Real specs leave those kinds quickly, though. As soon as a spec multiplies two
variables, talks about every element of an array, or needs induction, Z3 has
to rely on heuristics. Because of this, a proof that passes today can time out
tomorrow after an unrelated edit or a new version of the solver. When that
happens, the error says only that Z3 could not prove the goal. Teams that use
Verus on large projects keep this under control with strict habits: they keep
functions small and they pin the solver version. In Lean, a proof that checks
today keeps checking until someone changes the definitions it depends on.

Our second reason is that the SMT design would make us trust more code. Both
designs trust the language Spec and the translator. On top of those, the SMT
design trusts Z3 and the rules we would write to combine proof steps. Z3 is a
very large program, and when it says that no counterexample exists, it gives
us nothing we can check again. The Lean design trusts only Lean's kernel. The
kernel is small, and every proof it accepts is a record that a separate
checker can verify again.

Our third reason is that some of the facts we need are out of reach for a
solver. Consider the statement that if a step function keeps a record
valid, then folding it over any list of events keeps the record valid. That
statement is about all functions, and Z3's logic cannot express it. The fact
that the sum of two joined lists equals the sum of their parts needs its own
induction. Rounding bounds for splitting a total into equal parts mix multiplication with
integer division, which Z3 handles badly. In Lean, each of these is a short
theorem, and Mathlib often has a lemma for it already. We prove each one once
and reuse it. With Z3, we would have to break each proof into steps by hand,
and we would have to build the library ourselves.

Our last reason is that we can prove the translator itself correct. The
translator is written in Lean 4, and it is small because it accepts only a
limited subset of TypeScript. So the statement that it keeps the meaning of
every program it accepts is a Lean theorem about Lean code, and the proof is
within reach. Once we have that proof, we no longer need to trust the
translator, and the trusted part of tolean shrinks to the language Spec and
Lean's kernel. A solver could not do this work, because the proof goes by
induction over the syntax of programs.

## 3. What the choice costs

Lean asks for more proof. In the SMT design, a short invariant is often the
whole job, because Z3 fills in every step. In Lean, the same property needs a
theorem and a tactic script, even if the script is only one line. A codebase
with many small functions that have no loops and use only addition would make
this extra work add up.

We accept the cost for three reasons. First, Lean's tactics already handle
most of the routine proof. Second, the general theorems are the hard part, and
once we have proved them, each proof about a single function becomes short.
Third, Lean can call a solver itself. The `grind` tactic and projects such as
`lean-smt` send a goal to an SMT solver and then rebuild a proof that Lean's
kernel checks. That way we get the solver's help where it is useful, and we
still do not have to trust it.

## 4. Where Z3 still helps

Z3 is still useful as an independent check on the translator, although it
does not prove our theorems. We can ask Z3 whether any input makes a
TypeScript function and its Lean translation return different results. This
check only means something if we encode the two sides separately. We would
encode one side from the TypeScript, following the ECMA-262 sections that the
Spec cites. We would encode the other side from the Lean that tolean wrote. If
both sides went through tolean's own pipeline, a bug in that pipeline would
show up on both sides, and they would agree. When Z3 does find such an input,
we can add it to the test corpus. Z3 can also produce inputs that reach every
branch of a function, and we can run those inputs through Node and through the
compiled Lean.

We have not built this check yet. If we build it, it will live under `tests/`
and it will never replace a Lean proof. When Z3 gives up on a query, we will
record that as unknown and not as agreement.

## 5. When we would revisit this

We would reconsider the decision if most of the code we translate turned out
to be small functions with no loops, because then Lean's extra proof would buy
us nothing. We would also look again if solver tactics inside Lean became so
strong that the difference in effort disappeared. In that case, though, the
decision would stand and only our proofs would get shorter.
