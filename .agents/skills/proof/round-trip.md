# The parser's round trip

Goal: `parse (print t)` gives `t` apart from spans. `Syntax/Source.lean` prints a tree as lines of words, and a word is the token kinds that touch (`>=` is `>` then `=`). The parser's part is proven on tokens; the lexer's part is not.

## Files

| File | Main theorem | Covers |
|---|---|---|
| `Syntax/RoundTrip.lean` | `types_reads` | types; monad and `Leaves` basics |
| `Syntax/RoundTripExpr.lean` | `exprs_read` | each expression level; `afterOK` congruence; budget corollaries |
| `Syntax/RoundTripStmt.lean` | `stmts_read` | statements; `Laid`; `parseVarDecl_reads` |
| `Syntax/RoundTripDecl.lean` | `module_reads` | declarations, modules |

## The shape of a reading lemma

`ReadsW T erase words afterOK p x ends`: from any state whose `rest` is `ts ++ rest`, where `ts` are the tokens of `words x` and `rest` is nonempty, satisfies `ends`, and `afterOK` accepts it, `p` gives `x'` with `erase x' = erase x` and `Leaves s s' rest`. `ReadsE`, `ReadsP`, `ReadsS` (statements, with `inFunction` and `loopDepth`) and `ReadsD` (declarations) are its instances.

- **Line breaks.** `Touching ts words` says the tokens are the words in order, the tokens of each word touch (`Placed`), and inside a line a line break comes after a `lineBreak` (the empty word; the printer puts one only between `async` and the `(` of its call, ECMA-262 §15.9) and after no other word. Reading lemmas take `∀ y ∈ ts.tail, NoBreak y` (no line break before a non-`(`); it splits by membership, and a flag read on a non-`(` token is `noBreak_of hk (by decide) (hn y hy)`. A flag read on a `(` (after `async`, after `return`) comes from `Touching`: `Touching.after_callBreak`, `Touching.after_one`, `Placed.next`. `Laid ts lines` says a line break comes before each later line's first token.
- **Changing a hypothesis that many proofs split** (`fun y hy => hn y …`, ~60 sites): keep its `∀ y ∈ ts, P y` shape and weaken `P`; put the exact fact in `Touching`/`Placed`, which proofs split by words. `Placed w ws a b` sees the next words `ws`, so it can state what follows a word; on a fixed word it reduces, so the ~40 `simp [Touching] at h` sites need no change.
- **Where a level stops.** `Ends level e` says what may follow `e`: `EndsLhs`, `EndsPostfix`, `EndsBin m`, `EndsCond`, `EndsAssign`, `EndsExpr`. A conditional ends with an assignment, so `Ends .cond (.cond ..)` is `EndsAssign`. A statement that ends with an `if` without `else` (`openIf`) needs no `else` next.
- **What the parser looks at after a node.** `afterOK after e` checks `closesKinds` for `<` and `<<`, `notFirst "{"` after `(…)`, and the `async(…)` checks. `Expr.afterOK_congr` shows that it depends on `after` only through `AfterEquiv`, which compares the first token and `closesKinds 0`. So well-formedness states it with `[.punct ";"]` or `[.punct ")"]` (`afterOK_semicolon`, `afterOK_closer`).
- **First tokens.** `Expr.first` (a `startsExpr` token), `Expr.firstPostfix` (a `startsPrimary` token), `Expr.second` (no name as the second token after a name), `Stmt.first`, `Stmt.declStart`, `Decl.first`, `Field.first`. The token after an item (statement, field, declaration) is the next item's first token or the closer, which gives the `else` and `}` facts.
- **Well-formedness:** `TypeExpr.wf`, `Expr.wfAt T level`, `Stmt.wf T fn loop`, `VarDecl.wf`, `Decl.wf`, `Module.wf`. Each is the condition under which its theorem holds. Adding a condition weakens the theorem, so prove a fact the parser already guarantees (as `Expr.second` does) instead of adding it.

## Not proven yet

1. Every tree the parser gives satisfies the `wf` predicates.
2. The lexer's part: lexing `render lines` gives tokens that satisfy `Laid` for those lines, followed by the end of the file.

Until both exist, the theorems cover `wf` trees on tokens. Docs and PR text say that and nothing more.
