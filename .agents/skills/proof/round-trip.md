# The parser's round trip

Goal: `parse (print t)` gives `t` apart from spans. `Syntax/Source.lean` prints a tree as lines of words, and a word is the token kinds that touch (`>=` is `>` then `=`). Proven on source text for every tree the parser gives: `parseChars_reads`.

## Files

| File | Main theorem | Covers |
|---|---|---|
| `tolean/TypeScript/EStateM.lean` | `bind_ok`, `bind_eq`, … | monad lemmas for every `EStateM`; `Parse` and `Lex` export them |
| `Syntax/Layout.lean` | `Touching.kinds` | `NoBreak`, `Chained`, `Placed`, `Touching`, `Laid`; the lexer and parser proofs share them |
| `Syntax/RoundTrip.lean` | `types_reads` | types; `Kept`, `past`, `Leaves` |
| `Syntax/RoundTripExpr.lean` | `exprs_read` | each expression level; `afterOK` congruence; budget corollaries |
| `Syntax/RoundTripStmt.lean` | `stmts_read` | statements; `Laid`; `parseVarDecl_reads` |
| `Syntax/RoundTripDecl.lean` | `module_reads` | declarations, modules |
| `Syntax/RoundTripLex.lean` | `lexChars_render` | the lexer reads `render lines` as `Laid` tokens + eof, given `Word.ok` words and `breaksOK` lines |
| `Syntax/ParseWF.lean` | `parseTokens_wf` | parser output is `wf` and its printed words are `Word.ok` |
| `Syntax/RoundTripText.lean` | `parseChars_reads`, `source_reads` | `Module.breaksOK` (printer); the glue |

## The shape of a reading lemma

`ReadsW T erase words afterOK p x ends`: from any state whose `rest` is `ts ++ rest`, where `ts` are the tokens of `words x` and `rest` is nonempty, satisfies `ends`, and `afterOK` accepts it, `p` gives `x'` with `erase x' = erase x` and `Leaves s s' rest`. `ReadsE`, `ReadsP`, `ReadsS` (statements, with `inFunction` and `loopDepth`) and `ReadsD` (declarations) are its instances.

- **Line breaks.** `Touching ts words` says the tokens are the words in order, the tokens of each word touch (`Placed`), and inside a line a line break comes after a `lineBreak` (the empty word; the printer puts one only between `async` and the `(` of its call, ECMA-262 §15.9) and after no other word. Reading lemmas take `∀ y ∈ ts.tail, NoBreak y` (no line break before a non-`(`); it splits by membership, and a flag read on a non-`(` token is `noBreak_of hk (by decide) (hn y hy)`. A flag read on a `(` (after `async`, after `return`) comes from `Touching`: `Touching.after_callBreak`, `Touching.after_one`, `Placed.next`. `Laid ts lines` says a line break comes before each later line's first token.
- **Changing a hypothesis that many proofs split** (`fun y hy => hn y …`, ~60 sites): keep its `∀ y ∈ ts, P y` shape and weaken `P`; put the exact fact in `Touching`/`Placed`, which proofs split by words. `Placed w ws a b` sees the next words `ws`, so it can state what follows a word; on a fixed word it reduces, so the ~40 `simp [Touching] at h` sites need no change.
- **Where a level stops.** `Ends level e` says what may follow `e`: `EndsLhs`, `EndsPostfix`, `EndsBin m`, `EndsCond`, `EndsAssign`, `EndsExpr`. A conditional ends with an assignment, so `Ends .cond (.cond ..)` is `EndsAssign`. A statement that ends with an `if` without `else` (`openIf`) needs no `else` next.
- **What the parser looks at after a node.** `afterOK after e` checks `closesKinds` for `<` and `<<`, `notFirst "{"` after `(…)`, and the `async(…)` checks. `Expr.afterOK_congr` shows that it depends on `after` only through `AfterEquiv`, which compares the first token and `closesKinds 0`. So well-formedness states it with `[.punct ";"]` or `[.punct ")"]` (`afterOK_semicolon`, `afterOK_closer`).
- **First tokens.** `Expr.first` (a `startsExpr` token), `Expr.firstPostfix` (a `startsPrimary` token), `Expr.second` (no name as the second token after a name), `Stmt.first`, `Stmt.declStart`, `Decl.first`, `Field.first`. The token after an item (statement, field, declaration) is the next item's first token or the closer, which gives the `else` and `}` facts.
- **Well-formedness:** `TypeExpr.wf`, `Expr.wfAt T level`, `Stmt.wf T fn loop`, `VarDecl.wf`, `Decl.wf`, `Module.wf`. Each is the condition under which its theorem holds. Adding a condition weakens the theorem, so prove a fact the parser already guarantees (as `Expr.second` does) instead of adding it.

## Parser output is well formed (`ParseWF.lean`)

Each `*_gives` / `*_wf` theorem runs one parser function backwards from `p s = .ok x s'`.

- **`Ready s`**: the state is `Good`, ends with `s.eof` (kind `.eof`), and every token left is eof or `TokenKind.ok s.target`. `Ready.tok` gives `Word.ok T [x.kind]` for a token read; `readName_words` gives it for a name.
- **`Kept s s'`** (`RoundTrip.lean`; `Leaves` extends it): eof, `inFunction`, `loopDepth`, `target` unchanged. A loop's target fact comes from `hK.target_eq.trans hT`.
- **`afterOK`**: the parser read the same brackets, `;` and `>` that the printer writes (`skel`), and the printed tokens after a node stop the `>` scan where the source tokens stop it (`Follows`).
- **Words that lex back**: each result carries `WordsOK T` for its printed words (`GaveE.ok`, `GaveArgs.ok`, `StmtOK`, `DeclOK`). List items fold it into the Bool item predicate as `wf && words.all (Word.ok T)` (`both`, `both_left`, `both_right`). `words_ok` closes `WordsOK T ws` from hypotheses in context and fixed words; put the facts about sub-trees in context with `have` first.

## Scope

`parseChars_reads` covers every module the parser gives. `source_reads` covers every `wf` module whose printed words are `Word.ok`; `wf` alone does not check that a name is an identifier or that a number's text is one the lexer reads. The round trip shows the parser and printer agree, not that the parser reads TypeScript as `tsc` does; `tests/typescript/check.ts` tests that.
