# Repository layout

Each language has its own front end and its own translator, and both are
written in Lean. The front end reads the source into the language's syntax
tree. The translator then writes Lean directly, and the generated code
imports the language's Spec.

```
source ──front end──▶ syntax tree ──translator──▶ Lean ──imports──▶ language Spec
         (lexer and                  (one per
          parser)                    language)
```

The languages share no intermediate form, because each one models what code
does in its own way. A TypeScript function becomes a plain Lean function. A
Go function that calls an interface becomes a function in a state monad. A
SQL query becomes a function from a database to a result and a new
database. What the languages share is small: source positions, the printed
form of a syntax tree, the project file and the chain manifests.

| Path | What it holds |
|---|---|
| `tolean/Source.lean`, `tolean/Sexp.lean` | Shared by all languages: positions, spans, parse errors, and the printed form of a syntax tree |
| `tolean/Project.lean` | The project file, `tolean.json`: which units to translate, with which settings. Translation itself does no IO, so the WebAssembly build runs it too. |
| `tolean/Chain/` | The chain manifests: what each translation relies on, and the checks for them |
| `tolean/Audit.lean` | `#audit_claims`, which keeps claims apart from proofs |
| `tolean/<Language>/Spec/` | **The trusted model of the language's values** (for TypeScript: JS numbers). Generated code imports it, and proofs assume only what it states. Review it with care. |
| `tolean/<Language>/Syntax/` | The language's front end: tokens, lexer, syntax tree, parser, printer |
| `tolean/TypeScript/Translate.lean` | The TypeScript translator: it types the subset (with `null` narrowing) and builds the Lean definitions as a syntax tree |
| `tolean/TypeScript/Output.lean` | The syntax tree of the Lean code that the TypeScript translator writes, and its printer |
| `tolean/Go/Translate.lean` | The Go translator: one package at a time, from root functions, with interface calls as steps in a state monad |
| `tolean/Sql/` | The PostgreSQL front end, the schema translator that replays migrations, the query translator, and the READ COMMITTED model in `Spec/ReadCommitted.lean` |
| `Main.lean` | The `tolean` command |
| `wasm/` | The translator compiled to WebAssembly for the playground. `build.sh` builds it. |
| `npm/` | The npm package: the `tolean` command and `translateSource`, which run the native binary for the platform (built by `.github/workflows/release.yml`), and the Lean runtime that generated code imports |
| `playground/` | A static page where you edit an example and Lean checks its proofs in the browser |
| `tests/<language>/` | Checks for the front end against the language's own compiler, for the translator on a corpus, and for the Spec against the real runtime |

To add a language, create `tolean/<Language>/Spec/`,
`tolean/<Language>/Syntax/` and `tests/<language>/`. Also write a reference
printer that prints the language compiler's syntax tree in the same
S-expression form, as `tests/go/goast` does with `go/parser`.
