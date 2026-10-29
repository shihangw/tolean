# Loops and fuel

## Name the loop first

`Parse.iterate fuel acc step` runs `step` until it returns `false`. A lemma can only name a step that has a name, so turn an inline `fun acc => do …` into a top-level `def xStep` before proving (as `binaryStep`, `listStep`, `blockStep`, `importStep` and `declStep` are). Then check that the parser reads the same as before:

```bash
# Build the old binary first and copy .lake/build/bin/tolean aside. Run under bash: zsh does not split $files.
for f in $files; do for t in "" "--target ES2019"; do
  old parse $t --round-trip "$f" >a 2>&1; ea=$?; new parse $t --round-trip "$f" >b 2>&1; eb=$?
  [ $ea = $eb ] && cmp -s a b || echo "DIFF $f [$t]"; done; done
```

Run it over the repository's TypeScript files and about a thousand programs from `tests/typescript/gen.ts`. Done when no line says DIFF.

## Loop lemmas

- One step: `Parse.iterate_true : step acc s = .ok (acc', true) s' → iterate (n+1) acc step s = iterate n acc' step s'`, and `Parse.iterate_false` for the last step.
- **Continuation form**, for a chain built from the left (members, operators): induct on the tree and state `iterate (n + steps e) acc step s = iterate n e' step s'`. The outermost node's step runs last, so the induction hypothesis covers the inner chain and one `iterate_true` adds the node (`lhs_loop`, `bin_loop`).
- **Item lists** (`iterate_list`, `block_loop`, `field_loop`, `import_loop`, `decl_loop`): induct on the items, generalizing `fuel`, `acc`, the state and the tokens. Each item is followed by a `,` or by the closer: split the tail as `[]` or `y :: ys`.
- Fuel: the loop gets `budget = 10 * (left + 1)`. Show `items.length < fuel` from the token count (`length_items`, `Laid.length_le`, `Laid.length_decls`).

## Fuel for recursive calls

- Each parser function takes `fuel + 1` and calls the next with `fuel`. Give each level a cost and define `need level e = 9 * height + cost`, so every call stays inside the fuel the caller has.
- Prove the levels together by **strong induction on fuel**: show `∀ f, ∀ g ≤ f, AllRead T g` by plain induction on `f`, and dispatch `f + 1` to one lemma per level that takes `∀ g ≤ f` as its hypothesis (`exprs_read_le`, `stmts_read_le`).
- Callers that pass `(← budget)` need `need ≤ 10 * (left + 1)`. This comes from "a tree nests no deeper than it has tokens" (`Expr.height_le`, `TypeExpr.height_le`, `Stmt.depth_lt`), plus a `_budget` corollary (`parseExpression_budget`, `parseType_budget`, `parseBlock_budget`).
