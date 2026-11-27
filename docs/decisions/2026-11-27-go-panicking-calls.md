# Go calls of functions that can panic

**Status:** accepted · **Date:** 2026-11-27

The [record on Go panics](2026-11-26-go-panics.md) let a Go function panic
on a division by zero, but refused every call of such a function. This
record says how the translation carries a callee's panic to the caller.

## The decision

- The Go IR evaluator runs `Body.bind`, the shared IR's `>>= fun x =>`. When
  the callee returns `.error`, the caller ends with the same panic.
- The proved path accepts a call of a function that can panic only when it
  is the whole right side of `:=`, `=` or `var x T =`, or the whole value
  of `return`. The statement becomes a bind of the call, and the rest of the
  body follows in the bound name. A `return` binds the name `result` and
  then returns it.
- The arguments of such a call may divide, and the guard of the
  [panics record](2026-11-26-go-panics.md) tests their divisors first. They
  may not call another function that can panic, because a bind inside an
  expression would need an order of evaluation that the proof does not have.
- `CallsAgree`, the hypothesis that the IR's calls agree with the
  interpreter's, now covers a call that panics: `callR` returns
  `Option (Except Val Val)`. `translate_sound` therefore states that the
  caller panics with the callee's message.
- The string translation, which has no proof, finds the functions that
  reach a function that can panic, with a fixpoint over the call graph. Each
  such function runs in `Except String`, or in `ExceptT String (StateM σ)`
  when it has effects, and binds each such call with `←`, so a call may sit
  inside an expression. It refuses one in the right operand of `&&` or
  `||`, because `←` would run it even when Go skips that operand. The string
  translation has no division, so the order of the binds cannot change which
  panic comes first.

## What is left out

- A call of a function that can panic inside a larger expression, or in a
  compound assignment, on the proved path.
- The state piece of the shared core. Go does not need it yet; the
  [shared-core plan](../plans/shared-core.md) says when it will.
- `recover`, and panics other than division by zero.

## Alternatives

- **Binding every call inside an expression on the proved path.** It needs
  a monadic expression evaluator in the IR and its proof, for a form that
  Go code can always write as a separate statement.
- **Making every function `Except`.** Rejected in the panics record, for the
  same reason: it changes the output of code that cannot panic.
