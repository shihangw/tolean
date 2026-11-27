# Go functions with several results

**Status:** accepted · **Date:** 2026-11-26

A Go function may return several values, as in `func DivMod(a, b int) (int,
int)`, and `q, r := DivMod(a, b)` gives each to a local (Go specification,
"Function types", "Return statements", "Assignment statements" and "Short
variable declarations"). This record says how the proved path models them.

## The decision

- **One value for all the results.** The interpreter's values gain
  `Val.pair a b`, and the results `(a, b, c)` are `pair a (pair b c)`,
  nested to the right as Lean's `A × B × C` is. No Go variable holds a
  pair: only `return` makes one, and only an assignment of several names
  takes one apart. The translator's types gain the matching `Ty.pair`, and
  the output writes a Lean tuple with the shared IR's `tuple`.
- **`return a, b`** evaluates its values from left to right and returns
  their tuple. `return f(…)` returns a call whose results match.
- **`a, b := …` and `a, b = …`** take their values from one call of a
  function with as many results, or from as many expressions, evaluated
  from left to right. Then `:=` declares the locals, and `=` assigns them
  from left to right. Every value is evaluated before any local changes, so
  `a, b = b, a` swaps. The output takes the tuple apart with the shared IR's
  `letTuple`, `let (a, b) := e`, which TypeScript's object destructuring
  uses too.
- **The blank identifier** `_` takes a value and declares or assigns
  nothing. Neither the interpreter's environment nor the output binds it:
  Lean's `let (_, b) := e` binds no name either.
- The proof generalizes the lemmas for one local: `pushes_sim` declares
  several new locals at once, and `sets_sim` assigns several in order.

## What is refused

- **A `:=` that redeclares a local.** Go lets `a, b := …` assign `a` when
  `a` is declared in the same scope and `b` is new. The translator forbids
  shadowing, and telling the innermost scope apart needs a model of scopes
  that the interpreter does not have, so the interpreter gets stuck on it
  and the translator refuses it. A `:=` must also declare at least one
  local, as Go requires.
- **Two values that may each panic.** Go fixes the order of function calls
  only (Go specification, "Order of evaluation"). In
  `x, y = int(s[i]), a / b`, gc may test the divisor before the index, so
  when both fail, the panic message is not fixed by the order of the
  values. The random test found gc doing this. The interpreter evaluates
  from left to right, so the translator accepts at most one value with a
  check that can panic in one `return` or assignment. A single expression
  keeps its order, as before.
- **A call with several results of a function that can panic.** The call
  would need `>>=` with a tuple pattern. It comes with the error model.
- **Named results.** A bare `return` returns them, so they are locals that
  the function starts with. They can come later without changing the value
  model.
- **An assignment of several values in a counted loop's body.** The proof
  that the body does not change the counter covers one name at a time.

## Alternatives

- **A list of values.** `Val.tuple (vs : List Val)` would make the value
  type nested, and `DecidableEq` would need a manual instance. The right
  nested pair mirrors Lean's tuples, so the IR's evaluator gives the value
  of a tuple with no conversion.
- **Results as separate return slots.** The outcome of a function could
  carry a list of values. Every theorem about outcomes would change, while
  a pair changes only the places that make or take one apart.
