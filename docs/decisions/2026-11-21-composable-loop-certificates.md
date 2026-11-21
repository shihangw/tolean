# Loop certificates compose through one result carrier

**Status:** accepted · **Date:** 2026-11-21

Loop certificates must compose by the meaning of their results, not by the
names Lean gives generated helpers. The certifier will keep a proof lemma for
each loop, but every early-return loop will expose its outcome through one
shared carrier. Function and parent-loop proofs can then rewrite a loop result
without depending on which match helper Lean generated for that loop.

Each loop invariant describes the current evaluator environment. In
particular, a child-loop invariant must be established after the preceding
statement has updated the accumulator. An invariant that describes the
environment at the start of the parent loop is not enough for that child.

We considered proving one theorem for a whole chain of loops. That combines
different loop bodies and their state transitions in one proof interface, so
it does not scale to loops nested under branches or callbacks. We also
considered one specialized result theorem per loop. Those lemmas remain
useful for proving each evaluator fold, but distinct per-loop result
expressions cannot by themselves connect two returning loops in the
function-level link proof.

The prototype also generalized a pair-return lemma and asked `link_eqs` to
rewrite with full transparency. That approach did not establish a stable
rewrite boundary: it still depended on unfolding the generated expression
enough to identify the result. Instead, the generator will state the shared
outcome explicitly and use the per-loop evaluator lemma only at the loop
boundary.

The implementation must retain the existing certificate claims and rejection
rules. It must not add per-shape tactic sequences, axioms, partial definitions
or weaker tests. The required regressions cover sequential returning loops
over optional and nullable bigints, nested accumulator updates, the existing
28-cell loop matrix, and two additional unreported shapes. Loop returns from
inside nested loops remain follow-up work for #289 unless the shared result
interface supports them without a shape-specific proof.
