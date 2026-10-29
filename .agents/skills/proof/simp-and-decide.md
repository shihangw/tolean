# simp, rw and decide

## simp rewrites more than you asked

- `simp only [Token.isPunct]` on the whole goal unfolds every later `isPunct` too. It also rewrites those `if`s' `Decidable` instances, and after that `ite_guard` and `if_neg` stop matching. Decide each test with `if_pos` or `if_neg` and an exact `show` instead.
- `simp` turns `l.flatten.length` into a sum of lengths in the goal but not in a hypothesis, and then `omega` fails. State token-count equations (`Expr.tokens_member`, `Stmt.tokens_length_cons`), rewrite with them, and use `simp only [List.length_append, List.length_cons]`.
- `simp at h` produces left-nested conjunctions and disjunctions. Destructure them as written: `obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h`, `rcases h with (((rfl | rfl) | rfl) | rfl) | rfl`.
- `simp` turns `a.map kind = [k]` into `∃ x, a = [x] ∧ …` but keeps longer lists as equations. Handle both shapes: `first | obtain ⟨_, rfl, _⟩ := ha | …`.
- `simpa … using h` that `simp at h` alone would close is a linter warning, and `--wfail` makes it an error.

## Strings and decide

- `simp only` does not decide `"[" = "."`. Use `simp (config := { decide := true }) only […]`, or `punct_ne (by decide)`.
- String literal patterns defeat `cases h` on `"," = "}"` ("dependent elimination failed"). Use `absurd (h₁.symm.trans h₂) (punct_ne (by decide))`.
- `TokenKind` has `BEq` but no `DecidableEq`. So `by_cases h : x.kind = …` and `if x.kind = … then` fail. Use `Classical.em`, or state tests with `Token.isPunct` (a `Bool`).

## Derived BEq

A derived `BEq` is not known to be lawful, and `simp` cannot unfold it:

- `TokenKind` has `ReflBEq` and `LawfulBEq` instances in `RoundTrip.lean`.
- `Pos` has them in `RoundTripExpr.lean`, proved with `cases a; simp [BEq.beq, instBEqPos.beq]`.
- `BinOp.beq_eq : (a == b) = decide (a = b)` (by `cases a <;> cases b <;> rfl`) gives `LawfulBEq BinOp`.
- `VarKind` has none: close `VarKind.const == VarKind.let` by `decide`.

## Facts to reuse

`startsExpr`, `startsPrimary`, `stopsPostfix`, `separators` and `StartsStmt` are lists of token kinds. Each turns a family of `≠` facts into one `simp [startsExpr] at h`. Look for one before writing ten inequalities.
