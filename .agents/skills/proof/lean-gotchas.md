# Lean gotchas

Errors that look like math but are syntax, names or elaboration. Lean 4.30, no Mathlib.

- **Missing tactics and lemmas:** `tauto`, `le_rfl` and other Mathlib names do not exist. Use `rcases h with h | h <;> simp [h]` and `Nat.le_refl _`.
- **Keywords as constructor names:** `postfix` and `import` must be written `«postfix»` and `«import»`, as in `| «postfix» =>` and `.«import» sp names source`.
- **`cases … with` alternatives** do not accept `..`. Name every argument: `| forOfStmt _ _ _ _ _ =>`.
- **A multi-line structure update** inside a tactic `let` or `obtain` argument can fail to parse ("expected '}'"). Keep `{ s with … }` on one line.
- **A tactic sequence over several lines** after `<;>` or inside `( … )` does not parse. Use `all_goals` with an indented block.
- **Macros** referring to local names need `set_option hygiene false in` before the doc comment, and the macro goes after both.
- **A theorem `X.foo`** resolves `foo` in its own statement and body to itself (`Neutral.joined` with `joined`, `Touching.lineBreak` with `lineBreak`). Rename the theorem (`Touching.after_lineBreak`).
- **`simp only` does not fill `_` witnesses** of an anonymous constructor, as in `⟨_, _, by simp only [Expr.words], …⟩`. End the block with `; exact rfl`.
- **`⟨fun _ h => by cases h, by simpa …⟩`** parses as one `cases` with two targets ("Missing eliminator"). Wrap it: `(by cases h)`.
- **Recursion in a theorem** over a nested inductive (`Expr`, `Stmt`) works through `cases` on a subterm: Lean finds the structural recursion. Mutual theorems over `Expr` and `List Expr` go in a `mutual … end` block.
- **An implicit argument** that no hypothesis fixes stays a metavariable and breaks later `simp_all`. Pass it explicitly, as in `bin_loop (start := start)`.
- **Anonymous hypotheses** from `obtain ⟨x, ts', rfl, _⟩` shift what `rename_i` names. Name them.
- **A recursive call's `_` witnesses**, such as the span of a rebuilt node, are not inferred. Give them (`⟨start, s₂.lastStop⟩`).
