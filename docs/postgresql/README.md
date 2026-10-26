# PostgreSQL

tolean translates PostgreSQL queries written for sqlc, with the schema that
their migrations build. Each query becomes a function from a database to a
result and a new database. The [README](../../README.md) describes the parts
that all languages share.

[This graph](verification.svg) shows the verification chain for PostgreSQL. It
marks which links are proved, tested against a reference, or trusted.

## The translator

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
