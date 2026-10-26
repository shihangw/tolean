# tolean

tolean translates source code into Lean 4, so that proofs about a program are
about its real source. It reads a subset of each language and writes Lean
definitions that a person can read. It refuses everything else, and it
reports the file, the line and the reason. In CI, tolean generates the Lean
again and fails if the result differs from the committed copy. Then
`lake build` checks the proofs.

tolean reads three languages:

- **TypeScript**: pure functions become plain Lean functions.
- **Go**: code with effects is supported too. A function that calls methods on
  an interface, such as a database store, becomes a function in a state
  monad, so a proof can plug in a model of what the interface does.
- **PostgreSQL** queries written for sqlc, with the schema their migrations
  build: each query becomes a function from a database to a result and a new
  database. A model of READ COMMITTED isolation describes what concurrent
  transactions can do between statements.

A proof can join the last two: the Go code's theorem holds for any store that
keeps a stated contract, and a second theorem shows that the store built on
the translated queries keeps it.

The main use case is a double-entry ledger, and the test corpora use one. The
Go code checks that a journal entry's debits equal its credits, and then
posts each line through a store. The SQL statements debit and credit one
account each, inside one transaction, so the sum of all balances does not
change.

## Why tolean

Coding agents now write more code than people can review. A reviewer skims
the diff and approves it, and tests check only the inputs that someone
thought of. Neither shows that the code is correct for every input.

A proof does. A test shows that the right password logs a user in. A proof
shows that no wrong password ever logs a user in, for every possible input.
With tolean, you review what the code must do, and the Lean kernel checks
that the code does it.

tolean moves review from the code to the claim, and it keeps three things
out of the trusted path:

- **No model of the code written by hand or by an LLM.** The translator
  writes the Lean from the source that runs, and CI fails if the two differ.
  The translators are tested against reference implementations now; a proof
  that they are correct is the goal, and `tolean chain trust` lists what each
  claim still trusts.
- **No proof that you must read.** The kernel checks every step. An agent
  may write the proof, because a wrong proof does not pass.
- **No solver to trust.** A proof relies on a small kernel and the axioms it
  lists, not on the heuristics of an SMT solver (see
  [below](#why-a-proof-kernel-not-an-smt-solver)).

What remains is the claim, and a person must read it. A checker accepts a
true theorem that says nothing useful. For example, "the output is sorted"
holds for a sort that returns an empty list, because the claim never says
that the output has the same elements as the input. So write each claim as
one property of one component:

- a **precondition**, which is true when the code starts;
- a **postcondition**, which is true when it returns;
- an **invariant**, which stays true the whole time, such as "a session
  token is never accepted after the logout that revoked it".

Then read the claim before you read the code, and check it on a few inputs
that it must accept and a few that it must reject. A proof does not create
trust. It moves trust from the code to the claim, so if no person read the
claim, nothing was verified.

## The verification chain

What tolean produces is a verification chain: a path from the source code
that runs to theorems about it, where every link is proved, tested against a
reference, or trusted. The graphs show the chain for each language, and which
links are which:

- [TypeScript](docs/verification-typescript.svg)
- [Go](docs/verification-go.svg)
- [PostgreSQL](docs/verification-sql.svg)

Each language also splits into nested subsets: what the parser reads, what
the translator accepts, and what is proved. [This chart](docs/subsets.svg)
lists them.

### Chain manifests

The chain is also data. Each translation writes `<output>.chain.json` next to
the Lean file. It records the tolean version, the SHA-256 of each source file
and of the output, and the links the output relies on (parser, translator,
Spec, runtime), each with a status and the check that supports it.

A project adds `tolean.chain.json`. It lists the file manifests, its own links
(such as glue code or callers' preconditions), and its claims. Each claim names
a spec, the theorem that proves it, the module that holds the theorem, and the
axioms the proof may use:

```json
{
  "files": ["sensor/Raise.lean.chain.json"],
  "nodes": [{ "id": "callers", "kind": "glue", "status": "trusted",
              "label": "callers pass a gauge with level ≤ max" }],
  "edges": [["callers", "raise_stays_under_max"]],
  "claims": [{ "id": "raise_stays_under_max",
               "spec": "Spec.raise_stays_under_max",
               "proof": "Proof.raise_stays_under_max",
               "module": "sensor.RaiseProof",
               "axioms": ["propext", "Quot.sound"],
               "depends": ["sensor.Raise"] }]
}
```

The statuses are `proved`, `tested`, `trusted`, `read-by-people`, `generated`
and `planned`. A `tested` link names its check and who runs it: `tolean` for
tolean's own checks, which hold for the tolean version that wrote the
manifest, or `project` for the project's checks, which CI reports with
`--passed`.

```sh
lake build && lake env tolean chain check tolean.chain.json [--passed check,…]
tolean chain trust tolean.chain.json raise_stays_under_max
tolean chain graph tolean.chain.json | dot -Tsvg > chain.svg
```

`chain check` fails when a source or output changed since translation, when a
`tested` link has no passed check, or when a claim's theorem does not have
exactly the claim's type or uses an axiom the claim does not list. It reads
the theorems from the built `.olean` files. `chain trust` lists what a claim
relies on that no proof covers. `chain graph` draws the chain, colored by
status; [this is the graph](docs/chain-gauge.svg) of the sample project in
`tests/chain`, which `tests/chain/check.sh` checks.

To set up tolean in your own project, read
[Using tolean in a project](docs/project-layout.md). It shows the folder
layout and a full example for each language.

## Why a proof kernel, not an SMT solver

Tools such as Verus and Dafny send each verification goal to an SMT solver,
such as Z3. tolean writes Lean, and Lean's kernel checks every proof. This
gives a stronger guarantee in four ways:

- **A smaller trusted base.** A proof in tolean relies on the Lean kernel,
  which is a few thousand lines, and on the axioms that the proof lists.
  `#audit_claims` and `tolean chain check` report those axioms for each claim.
  An SMT result relies on the solver, which is hundreds of thousands of lines,
  and on the tool's encoding of the program into the solver's logic.
- **Proofs that can be checked again.** A Lean proof is an object. Any copy of
  the kernel, or an independent checker, can check it again. A solver
  usually answers only "no counterexample", with no certificate to check.
- **Stable results.** The kernel is deterministic. A proof stays valid until
  the definitions it is about change. A solver uses heuristics, so a proof can
  time out after a solver upgrade or after an unrelated lemma is added.
- **Proofs about the translator.** Lean can state and prove facts about
  languages, such as "for every program the translator accepts, the Lean has
  the meaning of the source". An SMT solver works on one formula at a time, so
  it cannot prove that the translator is correct. tolean's aim is a
  translator that is proved correct. Its parsers and translators are tested
  against reference implementations now, and the chain manifests mark them
  as tested, not as proved.

The cost is effort: someone must ask for each proof, where a solver often
finds one alone. Tactics such as `simp`, `omega` and `grind` make many proofs
one line long. [This decision record](docs/decisions/lean-not-smt.md) gives
the full comparison.

Neither design can show that a claim says what its author meant. A checker
accepts a true theorem that says nothing useful, such as "the output of sort
is sorted" without "the output has the same elements as the input". tolean
makes the claim the only text that a person must read. The translator writes
the model of the code, and the kernel checks the proof. The claim is a short
`def … : Prop`, which the chain marks as `read-by-people`.

## Layout

tolean is shaped like Babel. Each language has its own front end, and the
stages after it are shared.

```
source ──front end──▶ language AST ──lower──▶ shared IR ──generate──▶ Lean
         (lexer and                 (planned)            (planned)     │
          parser, in Lean)                                             │ imports
                                                     language Spec ◀───┘
```

| Path | What it holds |
|---|---|
| `tolean/Source.lean`, `tolean/Sexp.lean` | Shared by all languages: positions, spans, parse errors, and the printed form of a syntax tree |
| `tolean/Audit.lean` | `#audit_claims`, which keeps claims apart from proofs |
| `tolean/<Language>/Spec/` | **The trusted model of the language's values** (for TypeScript: JS numbers). Generated code imports it, and proofs assume only what it states. Review it with care. |
| `tolean/<Language>/Syntax/` | The language's front end, written in Lean: tokens, lexer, AST, parser, printer |
| `tolean/TypeScript/Translate.lean` | The TypeScript translator, in Lean: it types the subset (with `null` narrowing) and writes the Lean definitions |
| `tolean/Go/Translate.lean` | The Go translator: one package at a time, from root functions, with interface calls as steps in a state monad |
| `tolean/Sql/` | The PostgreSQL front end, the schema translator that replays migrations, the query translator, and the READ COMMITTED model in `Spec/ReadCommitted.lean` |
| `Main.lean` | The `tolean` command |
| `tests/<language>/` | Checks for the front end against the language's own compiler, and for the Spec against the real runtime |
| `npm/` | The npm package, the first published form |

To add a language, create `tolean/<Language>/Spec/`,
`tolean/<Language>/Syntax/` and `tests/<language>/`. Also write a reference
printer that prints the language compiler's syntax tree in the same
S-expression form, as `tests/go/goast` does with `go/parser`.

## Build and check

```sh
nix develop                                 # Lean 4.30.0, Node 24, pnpm 10
lake build --wfail                          # the library and .lake/build/bin/tolean
.lake/build/bin/tolean parse file.ts        # print the syntax tree, or file:line:col: reason
.lake/build/bin/tolean translate file.ts File.lean My.Namespace
cd tests/typescript && pnpm install
node check.ts                               # the Lean parser against tsc (see below)
node checkTranslate.ts                      # the Lean translator against the TS one (see below)
pnpm test                                   # JS number laws and bigint division against the engine
cd ../../npm && pnpm install && pnpm test && pnpm build
cd ../tests/go && go run ./check            # the Lean Go parser against go/parser (see below)
cd ../sql && go run ./pgcheck corpus        # the SQL translator against PostgreSQL (see below)
cd ../chain && ./check.sh                   # chain manifests on a sample project (see below)
```

CI runs all of these on each push and pull request, in the same Nix dev
shell, from `.github/workflows/check.yml`. It also runs the number laws on
every maintained Node release line (`nix run .#test-engines`), and it fails
if a check leaves a committed file changed.

## The TypeScript parser

`tolean/TypeScript/Syntax/` puts a span on every node. It reads:

- **Declarations:** functions, interfaces, type aliases, and `const` and `let`,
  each of them possibly exported.
- **Statements:** `const` and `let` declarations, expression statements,
  `return`, `if` and `else`, `for … of`, `while`, blocks, `break`,
  `continue` and the empty statement.
- **Expressions:** names; number, bigint, string, boolean and `null` literals;
  array and object literals, with shorthand and `key: value` properties;
  parentheses, member access, indexing and calls; the unary operators `!`,
  `-`, `+`, `~`, `typeof` and `void`; `++` and `--` before or after; the
  binary operators, including `??`, `**`, `in` and `instanceof`; the
  conditional operator; and assignment, with every compound operator.
- **Types:** keyword types such as `number`, `null`, literal types, named types
  with type arguments, arrays, unions and parentheses.

The translator accepts less than the parser reads; see
[The TypeScript subset](#the-typescript-subset). Sometimes `tsc` and JavaScript read the same tokens in two different
ways. When that happens, the parser refuses the code instead of choosing one
reading. There are two such cases:

- `f < A, B > (x)`. `tsc` reads type arguments, but JavaScript reads two
  comparisons.
- `(a)` followed by `{`. `tsc` reads an arrow function that is missing its
  `=>`, but JavaScript reads `(a); {`.

The parser also refuses code that tolean cannot represent exactly. Examples
are lone surrogates, legacy octal literals, template literals and non-ASCII
names.

`tests/typescript/check.ts` checks the parser against `tsc`. To do this,
`tests/typescript/tscAst.ts` prints the tree from `tsc` in the same
S-expression form, and it refuses the node kinds that the Lean parser does not
read. The check covers three kinds of input:

- For `corpus/parse/accept/*.ts`, both parsers must accept the file, and the
  two trees must be equal, spans included.
- For `corpus/parse/reject/*.ts`, the Lean parser must refuse the file. The
  first line of each file gives the line, column and reason to expect.
- Each run also makes 500 random programs, with line breaks and comments
  between tokens. For each one, the trees must be equal, or both parsers must
  refuse it, or the Lean parser must refuse one of the lookalikes above. The
  run prints its seed, so you can replay a failure.

## The Go parser

`tolean/Go/Syntax/` puts on every node the span that `go/ast` gives it, and it
inserts semicolons at line breaks as the Go specification requires. It reads:

- **Declarations:** `package`, imports, `const`, `var` and `type` (including
  aliases), each alone or grouped; functions and methods.
- **Types:** names and qualified names, pointers, arrays, slices, maps, structs
  (with embedded fields and tags), interfaces (with embedded interfaces),
  function types and `...` parameters.
- **Statements:** blocks, `:=`, `=` and the compound assignments, `++` and
  `--`, declarations, `return`, `break` and `continue`, `if` with an init
  statement and `else`, the three forms of `for`, `range` with `:=`, `=` or
  no variables, `switch` with an init statement and a tag, type switches and
  `defer`.
- **Expressions:** names; integer (decimal, hex, octal, binary, with
  separators), floating-point, rune, string and raw string literals; composite
  literals, including those whose element type is left out; selectors,
  indexing, two-index slicing, calls with `...`, unary and binary operators,
  type assertions and function literals. Like `go/parser`, it does not read `T{` as a
composite literal in the header of `if`, `for` or `switch` when `T` is a plain
type name, unless the literal is in parentheses.

The parser refuses generics, channels, `go`, `goto`, `select`, labels,
`fallthrough`, three-index slices, `[...]T` arrays, imaginary literals and
non-ASCII names. It reads type switches, type assertions, function literals
and `defer` even though the translator refuses them, so that a file can be
read when the translator needs only some of its declarations.

`tests/go/check` checks the parser against `go/parser`.
`tests/go/goast` prints the tree from `go/parser` in the same S-expression
form, with columns counted in code points, and it refuses the node kinds that
the Lean parser does not read:

- For `corpus/parse/accept/*.go`, both parsers must accept the file, and the
  two trees must be equal, spans included.
- For `corpus/parse/reject/*.go`, the Lean parser must refuse the file. The
  first line gives the line, the column and part of the message to expect.
- Any Go file named on the command line is checked like an accepted file.

## The Go translator

`tolean/Go/Translate.lean` translates one Go package at a time. It starts
from the functions named with `--root` and keeps only the declarations they
reach, so a file can hold code that tolean does not support:

```sh
tolean translate-go --root Post --erase-type Log --erase-package time \
  Ledger.lean Ledger ledger.go
```

The generated code imports `tolean/Go/Spec/Basic.lean`, the trusted model of
Go values. Review it with care.

- A function that calls a method on an interface parameter, such as a store,
  becomes a function in `StateM State`. The interface becomes a structure that
  holds the methods the code calls, so a proof can plug in a model of the
  store.
- A `range` loop over a slice becomes its own recursive function. `continue`
  is the recursive call, `break` returns the locals that the loop changes, and
  `return` leaves the function with its result.
- `int` and `int64` arithmetic wraps as Go's does, through `Go.wrap64`. A
  proof shows that the values stay in range and then reasons over `Int`.
- An `error` is `Option GoError`. tolean models how an error was made
  (`errors.New`, or `fmt.Errorf` with a leading `%w`) and drops the rest of
  the message.
- Code that only feeds observability is erased. A statement is erased when it
  reads a value of a type named by `--erase-type` or calls a package named by
  `--erase-package`. tolean refuses to erase a statement unless it only
  assigns through the erased value, so that erasing it cannot change any
  other value.

`tests/go/check` also translates each package in `corpus/translate/*/` with
the options in its `args` file. The result must equal the committed `.lean`
file in the same directory, and Lean must compile it. The corpus package,
`ledger`, posts a double-entry journal entry.

## The SQL translator

`tolean/Sql/` translates PostgreSQL queries written for sqlc, together with
the schema they read. You name the root queries, and tolean replays the
migrations in order to find the final shape of the tables those queries
reach:

```sh
tolean translate-sql Ledger.lean Ledger --query Debit --query Credit \
  --queries queries.sql --migrations migrations/*.up.sql
```

The generated code imports `tolean/Sql/Spec/Basic.lean`, the trusted model of
PostgreSQL values and errors. Review it with care.

`tolean/Sql/Syntax.lean` is the parser. It reads:

- **Schema statements:** `CREATE TABLE` with column constraints (`NOT NULL`,
  `DEFAULT`, `PRIMARY KEY`, `UNIQUE`, `REFERENCES … ON DELETE …`, `CHECK`) and
  table constraints, `PARTITION BY` and `PARTITION OF`; `CREATE TYPE … AS
  ENUM`; `CREATE DOMAIN`; `ALTER TABLE` to add or drop a column or a
  constraint, or to change a column's type, default or `NOT NULL`;
  `CREATE [UNIQUE] INDEX` on columns, with an optional `WHERE`; and `DROP`.
- **Queries:** `SELECT` with inner joins, `WHERE` and `FOR UPDATE [OF …]`;
  `UPDATE … SET … [FROM …] [WHERE …] [RETURNING …]`; and `WITH`, whose parts
  are `SELECT` or `UPDATE` statements.
- **Expressions:** columns, integer, string, boolean and `NULL` literals, typed
  literals such as `interval '1 day'`, `sqlc.arg(…)`, `::` casts, arithmetic,
  comparisons, `AND`, `OR`, `NOT`, `IS [NOT] NULL`, function calls, `EXISTS`
  and scalar subqueries.

It refuses `INSERT` and `DELETE` (not yet supported), `ORDER BY`, `GROUP BY`,
`LIMIT`, `DISTINCT`, `UNION`, outer and cross joins, `CASE`, `IN`, `BETWEEN`,
`LIKE`, JSON operators, `WITH RECURSIVE` and positional `$1` parameters. In a
migration, a statement it cannot read is kept as tokens, so that the schema
translator can skip it or refuse it as described below. The query translator
accepts less than the parser reads: of the functions, only `now()`, `LEAST`
and `COALESCE`.

- Each reached table becomes a row structure and a map from primary key to
  row. `Valid db` states what PostgreSQL enforces on every write: each row
  sits under its own key, `bigint` values stay in range, foreign keys point
  to rows, and unique columns are unique. Proofs may assume it.
- A migration statement that could change a reached table must parse, or
  tolean refuses it. Statements about other tables, data backfills and
  session settings are skipped.
- Each query becomes a function from the database to a result and a new
  database, or a PostgreSQL error such as `bigint out of range`. `now()` is an
  argument, because it stays the same within a transaction.
- Every table must be reached through its primary key. With `Valid db`, the
  lookup gives the same rows as a scan would. tolean refuses a full scan.
- Conditions use SQL's three-valued logic. PostgreSQL does not fix the order
  in which it evaluates `AND` and `OR`, so the model raises an error only
  when every order must. Whenever PostgreSQL succeeds, the model succeeds with
  the same result.

### Concurrency

The query functions describe one statement at a time. What concurrent
transactions can do between statements is described by
`tolean/Sql/Spec/ReadCommitted.lean`, a model of PostgreSQL's READ COMMITTED
isolation level as its documentation describes it. An `UPDATE` by key works on
the newest version of the row, under a lock it holds until its transaction
ends, and it re-checks its `WHERE` on that version. The model proves two
theorems about every interleaving of transactions:

- If every update keeps a property of a row, every committed row has it.
- Each committed row's measure, such as a counter, equals its first value
  plus what every committed transaction added. No update is lost.

The model covers the case READ COMMITTED does protect. It does not protect a
write whose value came from an earlier read of the same table without a lock.
So tolean refuses an `UPDATE` that uses a value read from its own table in the
same statement, through a `WITH` query or a subquery, unless that read uses
`FOR UPDATE`.

`tests/sql/pgcheck corpus` checks each directory in `tests/sql/corpus/`
against a real PostgreSQL that it starts for the test:

- The translation must equal the committed `.lean` file, and Lean must
  compile it.
- The schema that tolean built must match PostgreSQL's catalog after the same
  migrations.
- The directory's `Scenarios.lean` runs the generated code on many database
  states and writes what each query should return and leave behind. Each
  scenario then runs in PostgreSQL, in a transaction that is rolled back, and
  the two must agree.

It also requires tolean to refuse each query in `tests/sql/reject/`, with the
message in that directory's `expect` file. And it checks, on the real server,
the READ COMMITTED behavior the model relies on: of two transactions that take
20 from a counter with 30 left, a guarded `UPDATE` lets only one take, while a
read followed by an unguarded write lets both take and leaves -10.

## The TypeScript translator

`tolean/TypeScript/Translate.lean` translates the syntax tree. It does not
use `tsc`, so it types the subset itself. It gives every expression the type
that `tsc` would give it, with the same narrowing on `null`, and it refuses
anything it cannot type exactly. That type checker is part of what we trust.

`tests/typescript/checkTranslate.ts` checks the Lean translator against the
TypeScript translator in `npm/`, which uses `tsc`:

- The check runs on `corpus/translate/*.ts` and on 200 random typed programs
  per run, and it prints its seed. When both translators accept a file, they
  must write the same Lean, byte for byte, and Lean must compile it. When the
  TypeScript translator refuses a file, the Lean translator must refuse it
  too.
- The Lean translator may refuse more files than the TypeScript one. It may
  also accept a file that `tsc` refuses for a lint that does not change the
  meaning. Those lints are TS2367 and TS2845, which flag comparisons whose
  answer is fixed, and TS2322 when the target type is `true` or `false`.

### Effects (planned)

tolean refuses most calls to libraries with side effects today.
[The effects plan](docs/plans/effects.md) describes how the translators will
share one mechanism for them. Each library declares its effects in a small
file, and the declarations fix a trust boundary that a later proof of the
library removes.

### Names

A source name never hides a Lean name that the output uses. Before it
translates a file, the translator collects every identifier in it. When the
file declares a name that the output also uses, such as `List`, `Option`,
`some`, `none`, `decide`, `Int`, `Bool`, `String` or `JSNumber`, the output
writes the Lean name in full from the root, as `_root_.List` or
`_root_.Option.none`. The source name stays as it is, so a claim refers to
it by the name in the source. The number type parameter is `N`, or `N1`,
`N2` and so on when the file uses `N`. Both translators follow this rule, and
`corpus/translate/leanNames.ts` checks it. A Lean keyword, such as `def` or
`where`, is still refused as a name.

## Versions

Each translation is for one **target**, which is the ECMAScript edition that
the code runs on. tolean translates the source as it runs, because type
stripping keeps the syntax unchanged. This means the engine must support every
feature that the code uses. It also means that the translation must assume the
meaning that the target edition specifies.

```sh
tolean translate --target ES2022 input.ts Output.lean My.Namespace
```

- The target can be any edition from ES2015 to ES2025. The default is ES2024,
  because that is what Node 22 supports, and Node 22 is the oldest release
  line that is still maintained. We add a new edition only after we review
  what it changed.
- `tolean/TypeScript/Edition.lean` lists each JS feature that tolean relies
  on. For each feature, it gives the first edition that specifies it and the
  ECMA-262 production or operation that defines it. It uses names instead of
  section numbers, because section numbers move between editions. The parser
  and both translators refuse a feature that is newer than the target, and
  they all give the same message:

  | Feature | Since |
  |---|---|
  | `**`, `**=` | ES2016 |
  | bigint (literals, type, `+ - *`, comparisons) | ES2020 |
  | bigint `/` and `%` (`BigInt::divide`, `BigInt::remainder`) | ES2020 |
  | `??` | ES2020 |
  | `&&=`, `\|\|=`, `??=` | ES2021 |
  | numeric separators (`1_000`) | ES2021 |

  The number laws hold in every edition. If a later edition changes how
  something behaves, we add a new feature for the new meaning. We never give
  one feature a second meaning.
- Every generated file starts with the tolean release and the target, for
  example `-- Generated by tolean 0.1.0 for ES2024 from x.ts.` That way, the
  drift check notices when either one changes. A change to the meaning of a
  law is a major release. A new law, model or feature is a minor release.
- We test the laws on every engine listed in `engines` in `flake.nix`, which
  are Node 22 and Node 24. Run `nix run .#test-engines`. A law holds only for
  the engines that it passes on.

## The npm package

`npm/` is the `tolean` package. Its `package.json` sets `"private": true`, so
nobody can publish it by accident. To publish it, remove that line. The
package contains the `tolean` command, the `translateSource` function and the
Lean runtime in `lean/`. Its translator still reads TypeScript with `tsc`, and
it is the next part that we will move to Lean.

```sh
tolean <input.ts> <output.lean> <Lean.Namespace>
```

Generated code that uses `number` imports `tolean.TypeScript.Spec.Number`.
To use it, require the runtime by path:

```toml
[[require]]
name = "tolean"
path = "node_modules/tolean/lean"
```

## What is proved and what is trusted

This section describes the TypeScript pipeline. For Go and SQL, the trusted
parts are the spec files that generated code imports
(`tolean/Go/Spec/Basic.lean` and the files in `tolean/Sql/Spec/`), the
translators, and, for a proof that joins them, the glue code a project writes
between the Go interface and the generated queries.

![The tolean pipeline: proof path, planned certificate, and what runs](docs/pipeline.svg)

| Step | What happens | Status | How it is checked |
|---|---|---|---|
| 1. Parse and type-check | `tsc` reads the source and gives the AST and the types | Trusted | `tsc` is the reference TypeScript compiler. tolean refuses a file with type errors. The Lean parser, checked against `tsc`, is to replace it. |
| 2. Translate | tolean writes readable Lean definitions (the generated `.lean` files) | **Trusted, not proved** | The rejection tests in `npm/src/translate.test.ts`, the CI drift check, and review. Nothing proves yet that the Lean means the same as the TypeScript. |
| 3. Prove the claims | Hand-written proofs show that each claim in `Spec/*.lean` holds for the generated definitions | **Proved** | The Lean kernel, `#audit_claims`, `lake build --wfail`, and no `sorry`, `admit`, `axiom` or `native_decide` |
| 4. Assume JS number facts | `SafeIntLaws` and `SpecialValueLaws` in `tolean/TypeScript/Spec/Number.lean` | Trusted, tested | `tests/typescript/jsNumberLaws.test.ts` checks each law against real doubles. |
| 5. Run | Type stripping or a bundler makes the JavaScript that Node runs | Trusted | The subset uses only constructs that type stripping leaves unchanged |
| 6. Call | The caller passes inputs that meet the theorems' preconditions | Not checked | Planned: boundary guards |

So a theorem holds for the code that runs if steps 1, 2, 4 and 5 are correct
and the inputs meet its preconditions. Step 2 is the large step that we trust
without proof. The plan below turns it into a proof, so that we no longer need
to trust the translator:

| Planned piece | Purpose | Status |
|---|---|---|
| Differential test | Run the TypeScript in Node and the generated Lean on the same random inputs, and compare. Evidence for step 2, with a failure report that an agent can reproduce. | Not started |
| AST as Lean data | The syntax tree of each file as Lean data (`Program`) | Started: the Lean parser gives it |
| `eval`, a JS interpreter in Lean | The meaning of a `Program`. It is trusted, so it is tested against Node. | Not started |
| Construct lemmas | Proved once, for example: an interpreted `for…of` equals `List.foldl` | Not started |
| Per-file certificate (`f.source`) | Proves `eval(Program)` equals the generated definition, for all inputs. Step 2 is then proved. | Not started |
| Boundary guards | Check the preconditions of step 6 where callers enter the verified code | Not started |

## The TypeScript subset

The TypeScript translation is a shallow embedding, which means it maps
TypeScript constructs straight to Lean constructs. That is sound only for code
that cannot alias mutable state. For this reason, the subset lets a function
change only the locals that it owns. tolean rejects anything else and reports
the file, the line and the reason. It never approximates.

| TypeScript | Lean |
|---|---|
| `bigint` | `Int` (exact; literals are typed `(n : Int)`) |
| `number` | an abstract `N` with `[JSNumber N]` (see [Numbers](#numbers)) |
| integer `number` literal, `-x`, `+ - *`, `< <= > >=`, `=== !==` on `number` | `JSNumber.ofSafeInt`, `neg`, `add`, `sub`, `mul`, `lt`, `le`, `eq` |
| `Number.isSafeInteger(x)` | `(JSNumber.toSafeInt x).isSome` |
| `Number.isNaN(x)`, `Number.isFinite(x)` | `JSNumber.isNaN x`, `JSNumber.isFinite x` |
| `NaN`, `Infinity`, `-Infinity` | `JSNumber.nan`, `posInf`, `negInf` |
| `T \| null`, `null` | `Option T`, `none` |
| `x === null`, `x !== null` | `x.isNone`, `x.isSome` |
| `x === null \|\| e`, `x !== null && e` | `match x with \| none => … \| some x => e` (TypeScript's narrowing) |
| `boolean` | `Bool` |
| `string` | `String` |
| `ReadonlyArray<T>`, `Array<T>`, `T[]` | `List T` |
| `interface` with `readonly`, required fields | `structure` |
| `function` with typed parameters and return type | `def` |
| `const x = e`, `let x = e` | `let x := e` |
| `x = e`, `x += e`, `x -= e`, `x *= e` on a `let` local | `let x := …` (shadowing) |
| `const xs: Array<T> = []`, then `xs.push(e)`; `xs` read only in the `return` | `let xs := xs ++ [e]` |
| `for (const x of xs) { … }` | `List.foldl` over the tuple of locals the body changes |
| `if` that returns, `if` that changes locals, `c ? a : b` | `if … then … else …` |
| `+ - *`, `< <= > >=`, `=== !==`, `&& \|\| !` | the same operators on `Int`, `Bool`, `Prop` |
| `a / k`, `a % k` on `bigint`, where `k` is a nonzero literal | `Int.tdiv a k`, `Int.tmod a k` (both truncate toward zero, as JS does) |
| `{ a, b: e }` building a declared interface | structure instance |
| Call to a function declared earlier in the file | application |

tolean rejects these, among others:

- Fractional or unsafe `number` literals, such as `0.5` and `2 ** 53`. It also
  rejects `/`, `%` and `Math.*` on `number`, because no law covers them yet.
- `/` and `%` on `bigint`, unless the divisor is a nonzero literal. JS throws
  an error when the divisor is `0n`, but `Int.tdiv` returns 0.
  `tests/typescript/bigintDivision.test.ts` checks on random pairs that JS
  `/` and `%` agree with `Int.tdiv` and `Int.tmod`.
- `===` on objects, because in JS it compares references. It also rejects
  `===` between nullable values.
- The global `isNaN` and `isFinite`. These convert their argument to a number
  first. Use `Number.isNaN` and `Number.isFinite` instead.
- Assignment to a parameter, a `const` or a field, and a push onto an array
  that the function did not create. It also rejects `break`, `continue`, and
  `return` inside a loop.
- A read of an owned array anywhere except in the `return` value. If code
  kept an alias, stored the array in a field or looped over it, it would miss
  a later push. In Lean a push makes a new list, but in JS it changes the
  shared one.
- Recursion, closures and arrow functions, classes, `async`, imports,
  exceptions, and optional or mutable interface fields.

The rejection tests in `npm/src/translate.test.ts` state in executable form
what the translator refuses. To see what that does and does not guarantee,
read [What is proved and what is
trusted](#what-is-proved-and-what-is-trusted).

## Numbers

A JS `number` is an IEEE-754 double. tolean does not map it to Lean's
`Float`, because then the code would run in Lean, but you could not prove
anything about it. Lean's `Float` is an opaque wrapper around C doubles. Its
operations are `extern` functions that come with no lemmas, so even
`(1.0 : Float) + 1.0 = 2.0` has no proof without `native_decide`. You could
prove only facts that hold for any type, such as "the result is one of the
inputs".

Aeneas has the same problem with Rust's `f64`, and it does not support floats
yet ([AeneasVerif/aeneas#828](https://github.com/AeneasVerif/aeneas/issues/828)).
The discussion there shows two ways that things go wrong. First, float
literals and arithmetic fail to translate. Second, code that only passes an
`f64` along translates to a Lean type `F64` that the Aeneas library never
defines. Because Lean's `autoImplicit` option is on by default, that name
silently becomes a type variable. One proposed fix maps `f64` to Lean's
`Float`. With that fix the code runs, but you still cannot reason about the
arithmetic.

tolean takes a different approach. Every definition that uses `number` is
generic over an abstract number type `N`, which has the operations of the
`JSNumber` class in `tolean/TypeScript/Spec/Number.lean`. Proofs can use this
at three levels:

- **Nothing assumed.** A theorem that you prove for every `N` also holds for
  real doubles. This level is enough for facts that do not depend on
  arithmetic.
- **Safe integers.** `toSafeInt : N → Option Int` returns the integer that a
  value is, when `Number.isSafeInteger` holds for it. `SafeIntLaws` states
  two facts about safe integers. JS arithmetic on them is exact as long as
  the result stays in range, and comparison on them agrees with `Int`. A
  theorem that needs this takes `[SafeIntLaws N]` and hypotheses such as
  `toSafeInt x = some i`. Then it reasons over `Int`.
- **`NaN` and `±Infinity`.** `isNaN`, `isFinite`, `nan`, `posInf` and `negInf`
  model `Number.isNaN`, `Number.isFinite`, `NaN` and `±Infinity`.
  `SpecialValueLaws` states how they behave. `===` is symmetric, and it is
  reflexive for every value except `NaN`, so `x !== x` tests for `NaN`.
  `NaN` fails every comparison and spreads through `+`, `-` and `*`.
  `±Infinity` bound every finite number, and `Infinity - Infinity` is `NaN`.
  A theorem that needs these facts takes `[SpecialValueLaws N]`.

The laws are hypotheses, not Lean axioms. If one of them were false, the
theorems that use it would not apply to JS. But Lean would stay consistent,
and every other theorem would still stand.

Lean cannot check facts about the JS engine. Instead,
`tests/typescript/jsNumberLaws.test.ts` checks each law against real doubles,
including the range limits, `±0`, subnormal numbers, `NaN` and `±Infinity`.
Each check records the exact Lean statement that it was written for, so
nobody can change a law without also changing its check.

`tolean/TypeScript/Spec/Lemmas/Number.lean` contains facts that we proved from
the laws, and any project can reuse them. Examples are reflexivity on safe
integers and `eq a a = !isNaN a`. These facts assume nothing new, so they need
no audit.

## Claims and proofs

The Lean package also provides `#audit_claims Spec Proof`, in
`tolean/Audit.lean`. This command keeps what is claimed apart from how it is
proved. A claim is a `def … : Prop` in the namespace `Spec`. The command fails
the build unless each claim has a theorem with the same name in `Proof`, and
the theorem's type must be exactly that claim. Because of this, reviewers only
need to read the `Spec` files and `tolean/TypeScript/Spec/`, which is the
trusted model of JavaScript.

## Prior work

tolean takes its design from two projects. It uses their ideas, but not their
code.

- [Aeneas](https://github.com/AeneasVerif/aeneas), together with
  [Charon](https://github.com/AeneasVerif/charon), translates safe Rust into
  pure Lean. Rust's borrow checker rules out aliasing, so Aeneas can turn a
  mutation in place into a pure update of a value. TypeScript has no borrow
  checker, so tolean gets the same property from its subset instead. Only
  locals that the function owns can change, and the function can read an
  owned array only in its return value.
- [Ariadne](https://github.com/nathsou/ariadne) translates a TypeScript subset
  into readable Lean definitions, and it rejects what it cannot model. Ariadne
  also proves, once for all programs, that its definitions match a JavaScript
  interpreter, and it emits a `source` theorem for each function. tolean does
  not do that yet. For now, we trust the match between JS and Lean, but we
  have not proved it.

## License

Apache License 2.0. See [LICENSE](LICENSE).
