# Lean gotchas

Errors that look like math but are syntax, names or elaboration. Lean 4.30, no Mathlib.

- **Missing tactics and lemmas:** `tauto`, `le_rfl` and other Mathlib names do not exist. Use `rcases h with h | h <;> simp [h]` and `Nat.le_refl _`.
- **Keywords as constructor names:** `postfix` and `import` must be written `«postfix»` and `«import»`, as in `| «postfix» =>` and `.«import» sp names source`.
- **`cases … with` alternatives** do not accept `..`. Name every argument: `| forOfStmt _ _ _ _ _ =>`.
- **A multi-line structure update** inside a tactic `let` or `obtain` argument can fail to parse ("expected '}'"). Keep `{ s with … }` on one line.
- **A tactic sequence over several lines** after `<;>` or inside `( … )` does not parse. Use `all_goals` with an indented block.
- **Macros** that read local hypotheses take their names as arguments (`macro "op_tokens " ha:ident hc:ident hs:ident : tactic`), spliced as `$ha` (`$ha:ident` in an `obtain` pattern or after `at`). Keep hygiene on.
- **`rfl` in an `obtain` pattern inside a hygienic macro** is a name, not a substitution, so nothing is substituted and a later `simp` makes no progress. Name the equation and `subst` it.
- **`obtain ⟨…, h⟩ := f h`** keeps the old `h`, and a later `subst` can move the old one after the new one, so `h` then names the old fact. `replace h := f h` first, then `obtain … := h`.
- **A theorem `X.foo`** resolves `foo` in its own statement and body to itself (`Neutral.joined` with `joined`, `Touching.lineBreak` with `lineBreak`). Rename the theorem (`Touching.after_lineBreak`).
- **`simp only` does not fill `_` witnesses** of an anonymous constructor, as in `⟨_, _, by simp only [Expr.words], …⟩`. End the block with `; exact rfl`.
- **`⟨fun _ h => by cases h, by simpa …⟩`** parses as one `cases` with two targets ("Missing eliminator"). Wrap it: `(by cases h)`.
- **Recursion in a theorem** over a nested inductive (`Expr`, `Stmt`) works through `cases` on a subterm: Lean finds the structural recursion. Mutual theorems over `Expr` and `List Expr` go in a `mutual … end` block.
- **An implicit argument** that no hypothesis fixes stays a metavariable and breaks later `simp_all`. Pass it explicitly, as in `bin_loop (start := start)`.
- **Anonymous hypotheses** from `obtain ⟨x, ts', rfl, _⟩` shift what `rename_i` names. Name them.
- **`match x with` in a `have` statement**, where `x` is a local, also matches on each hypothesis whose type mentions `x` (`match x, hr with`), so it is not the term in the definition and `cases h : x` fails ("not type correct"). Split the goal itself with `cases x`.
- **A `by` block's next line** must be indented past the column where its first tactic starts, or it ends the tactic ("unexpected token '('; expected '⟩'"). Start the block on its own line: `(by⏎ simpa … using f⏎   (arg))`.
- **An implicit state fixed too early**: in `listStep_wf hp hT hI hst`, `s₀` is fixed by `hT : s₁.target = T`, which is defeq to the wanted state's target, and then `hI` mismatches. Pass `(s₀ := …)`.
- **`simp` lemmas about `<$>`** can be in use where the code has no `<$>`: core `bind_pure_comp` turns `x >>= fun a => pure (f a)` into `f <$> x`. Build before deleting one.
- **A recursive call's `_` witnesses**, such as the span of a rebuilt node, are not inferred. Give them (`⟨start, s₂.lastStop⟩`).
