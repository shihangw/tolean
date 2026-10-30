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
| `docs/` | The docs, which VitePress also builds into the [docs site](#the-docs-site). The site's config is in `docs/.vitepress/`. |
| `tests/<language>/` | Checks for the front end against the language's own compiler, for the translator on a corpus, and for the Spec against the real runtime |

To add a language, create `tolean/<Language>/Spec/`,
`tolean/<Language>/Syntax/` and `tests/<language>/`. Also write a reference
printer that prints the language compiler's syntax tree in the same
S-expression form, as `tests/go/goast` does with `go/parser`.

## The docs site

The Markdown files in the repository are the only source of the
[docs site](https://shihangw.github.io/tolean/docs/). VitePress builds
`README.md` and every Markdown file under `docs/` into it. The `docs` job in
CI builds it on each pull request, and on `main` the site is published
under `/tolean/docs/`, next to the playground. To build it yourself, run
`pnpm install` and then `pnpm build` in `docs/`. `pnpm dev` serves it and
rebuilds a page when you save the file.

A page's URL follows from its file's path, and a `README.md` is the page of
its folder. So `docs/typescript/README.md` is `/typescript/`, and the root
`README.md` is `/overview`. The build writes two files into `docs/` that
nobody commits: `overview.md`, which is a copy of the root README, and
`index.md`, which is the front page. If you move a file, add its old URL to
`redirects` in `docs/.vitepress/config.ts`, so that the old URL still works.

Write links as GitHub reads them, relative to the file. The build turns a
link to another doc into a link to its page, and a link to any other file
in the repository into a link to that file on GitHub. GitHub's anchors
work too, because the site gives headings the same anchors as GitHub does.

Each page gets a category from where its file lives:

| Category | Files |
|---|---|
| Overview | `README.md` |
| Languages | `docs/<language>/README.md` |
| Guides | Other files in `docs/` |
| Comparisons | `docs/vs_*.md` |
| Plans | `docs/plans/` |
| Decisions | `docs/decisions/` |

If the folder gives the wrong category, put a comment such as
`<!-- category: Guides -->` on the file's first line. The sidebar and the
front page list each page under its category, with the page's first
heading as its title. The front page also shows the first sentence of the
page's first paragraph, so that sentence should say what the page is about.
A plan or a decision shows its status, which comes from the line
`**Status:** …` under the title.

The build fails in four cases, so a pull request with one of them fails
too:

- A link names a file that does not exist, or an anchor that its page does
  not have.
- Two files would be the same page, such as `README.md` and `index.md` in
  one folder.
- A plan has no status line.
- A file has no top-level heading.
