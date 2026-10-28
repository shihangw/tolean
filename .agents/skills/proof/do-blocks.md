# Stepping through a do-block

The parser is `ParseM := EStateM ParseError ParseState`. A proof runs it on a known state and shows `p s = .ok x s'`.

## The rewrite chain

Unfold the function with `simp only [Parse.f]`, then rewrite one bind at a time:

```lean
rw [Parse.bind_eq (Parse.peek_eq hs), Parse.bind_eq (Parse.advance_eq hs),
  Parse.bind_eq hp, Parse.bind_eq (Parse.spanFrom_eq _ _)]
rfl
```

`Parse.bind_eq : x s = .ok a s' → (x >>= f) s = f a s'`. Name every state with `let sₖ := advanced s x u r` (or `{ s with rest := …, left := …, lastStop := … }`), and get sub-results (`hp : Parse.parseAssign g s₂ = .ok e' s₃`) at exactly those states. The chain matches syntactically, so a state the goal spells differently stops it.

One big `simp [Parse.f, bind, EStateM.bind, …]` works only for short functions whose states stay simple. It normalizes nested `{ { s with … } with … }` states, and then a hypothesis about `sₖ` no longer matches.

Step lemmas: `peek_eq`, `peekAt_rest`, `advance_eq` (needs two tokens), `advance_cons` (needs a nonempty rest), `expectPunct_ok`, `discard_eq`, `budget_eq`, `spanFrom_eq`, `requireFeature_ok`, `modify_eq`, `pure_eq`, `pure_bind`, `endStatement_semi`, `readName_ok`, `readPropertyName_ok`, `skip_ok`, `withLoop_ok`.

## Guards and `if`

- **The do-compiler copies the continuation into both branches.** `if c then failAt t "…"` followed by more code becomes `if c = true then failAt … >>= k else pure () >>= k`. Close it with `rw [Parse.ite_guard (fun h => …)]`, where the argument proves the guarded action passes (or derives `False`).
- **Decide one `if` exactly:** `rw [if_pos (show x.isPunct ":" = true by simp [Token.isPunct, hx])]` or `if_neg (show ¬ … by …)`. Spell the condition with `show`. A bare `(by simp)` has a metavariable type and fails.
- **After `if_neg` comes `pure PUnit.unit >>= k`;** rewrite it with `Parse.pure_bind`.
- A guard whose branches differ (such as `if (← peek).isIdent "as" then refuseImport (← peek)`) is not `ite_guard` shaped: use `if_neg` plus `pure_bind`.
- `let mut x := none; if c then x := some …` also copies the rest of the block into both branches. Split the proof into one case for each path. Write the paths as separate lemmas, then a dispatcher picks one.

## Side goals from the goal itself

To get a step's result without restating the parser's code, leave it as a side goal: `rw [Parse.bind_eq (a := ()) (s' := s) ?g1]`, then `case g1 => …`. Use this when restating a guard would need the parser's own `match`.

## `match` in the parser

- `match t.kind with` on string patterns, inside a do-block applied to a state: `split` cannot split it. Write `generalize x.kind = k at h ⊢`, then `cases k`. In each case, `simp [h₁, h₂]` with the string inequalities (`p ≠ "{"`) reduces the match.
- `split` takes the first free `if` it finds, even one inside a match arm.
- `x matches .keyword _ | …` reduces under `simp only` once `x.kind` is a constructor, so rewrite the kind first.
- An early `return ← p` compiles to `p >>= fun r => pure r`.

## `Leaves`

`Leaves s s' rest` records what a read keeps: `rest`, `left`, `eof`, `inFunction`, `loopDepth` and `target`. Chain the steps with `leaves_trans` over `leaves_advance` and `leaves_advanced`. When a step changes a field, as `withLoop` and the `inFunction` flag of `parseFunction` do, build the record by hand (`leaves_withLoop`, `leaves_inFunction`).
