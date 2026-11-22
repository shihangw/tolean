# Loop certificates compose through one result carrier

**Status:** accepted · **Date:** 2026-11-21

Loop certificates compose through `LoopResult`, which distinguishes a returned
value from a completed loop's state. The generator exposes that result instead
of relying on the names Lean gives each generated match helper.

The certifier emits the same proof step for each loop in program order. It
evaluates the preceding statements without unfolding folds, rewrites with
`bodyExec_fold_compose`, and applies that loop's lemma to the current
environment. It then splits the shared result into returned and completed
cases. Only the completed case reaches the next statement.

A child loop follows the same steps inside its parent's loop lemma. Its
invariant describes the environment after any preceding loop or accumulator
update, not the environment at the start of the parent iteration.

The result split rewrites both sides by definitional equality before it
inspects the carrier. This matters because the evaluator lemma and the
translated definition can use distinct match helpers for the same loop body.
An ordinary simplifier rewrite does not always identify those helpers.

We first proved the two optional-bigint loops by hand. The generated steps
also certify two nullable-bigint loops and an optional outer loop with two
inner folds around an accumulator update. Required fixtures cover those
three cases, three returning loops with mixed optional and nullable elements,
and two returning loops that share an accumulator.

The earlier prototype unfolded the evaluator with one large simplification
and then tried to rewrite the resulting folds. That lost the boundary between
one completed loop and its continuation. Changing the carrier definitions in
the simp set did not repair it. We retain per-loop evaluator lemmas, but apply
them before unfolding the fold's continuation.

This change does not add axioms, partial definitions or weaker certificate
claims. The translator still refuses an inner loop that returns from the
function when the statements after that loop do not end in a return. That
translation restriction is separate from certificate composition.
