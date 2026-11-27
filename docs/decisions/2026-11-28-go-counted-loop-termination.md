# Go counted loops with computed bounds

**Status:** accepted · **Date:** 2026-11-28

The first proved counted loop stood only at the start of a function and took
literal bounds, at most 256 iterations. This record lets it stand anywhere and
take bounds that the program computes, and says why it terminates.

## The decision

- The interpreter evaluates both bounds once, before the first iteration. It
  then runs the body over the finite list `upTo a b`, the integers from `a`
  up to but not including `b`. The interpreter is structural on that list, so
  the loop terminates without fuel and without a new `partial def`.
- This matches Go only when the body cannot change the bounds or the
  counter. The translator and the interpreter both check that: the body must
  not assign the counter or any local that a bound reads, and a bound must
  not read the counter. Go then evaluates the condition with the same bound
  values on every iteration, so the list gives the same iterations.
- A bound contains no division or other operation that can panic. The proof
  of a bound then needs only the expression theorem's plain result.
- The translation emits the same list. For two literal bounds and at most
  256 iterations, it prints the list element by element, so earlier output
  stays byte for byte the same. Otherwise it prints `(Go.upTo a b)`, which
  avoids Lean's recursion limit on long literal lists. The limit no longer
  refuses any loop.
- `stmts_sound` takes the loop law as a premise, and `LoopFrame.loop_law`
  proves it. This keeps the module order: `LoopFrame` imports `Stmt`.

## Rejected options

- Fuel for the loop. Fuel would make a long loop look like a nontermination
  in the interpreter, and the theorem would need a fuel bound for each call.
  The finite list makes fuel unnecessary.
- A loop with only a condition. Its iteration count depends on the body, and
  the proved path has no measure that decreases. It stays refused.
