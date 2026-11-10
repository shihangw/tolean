# Plan: prove the SQL translator

**Status:** in progress · **Date:** 2026-11-09

The SQL translator is proved for `SELECT` queries only. A proved query is
one `SELECT`, `:one` or `:many`, without `WITH` and without subqueries. Each
of its tables must be reached through its primary key. The
[PostgreSQL guide](../postgresql/README.md#what-is-proved) describes that
part. Every other query still goes through the string translation in
`tolean/Sql/Translate.lean`, which Lean cannot reason about, because it
builds text with `partial def`.

This plan moves the rest of the subset onto the proved path, one construct
at a time, until the string translation can be deleted. It is the SQL part
of step 8 of the [shared core plan](shared-core.md).

## The rules for every addition

1. **PostgreSQL defines the behavior.** The interpreter in
   `tolean/Sql/Spec/Eval.lean` follows the PostgreSQL documentation, and it
   never looks a row up by its key. A construct whose meaning depends on
   static types that the values do not show stays refused, or the
   interpreter learns those types first.
2. **The printed code agrees with PostgreSQL.** The proved path refuses a
   construct where the printed code would compute something else on some
   database, even when the string translation accepts it.
3. **The proof covers it.** Each construct extends `Plan.lean`, the IR and
   its evaluator, and the interpreter, so that `translate_sound` holds for
   queries that use it.

## What to add

A construct leaves this table when the proved path translates it, and the
PostgreSQL guide documents it from then on.

| Construct | What the interpreter does | What the proof needs |
|---|---|---|
| `EXISTS` and scalar subqueries | Evaluates the subquery for each row of the outer query, with the outer aliases in scope, and raises `cardinality` when a scalar subquery finds two rows | Scopes with levels, because a name resolves in the innermost query first |
| `UPDATE … WHERE alias.key = e`, with `RETURNING`, as `:one`, `:exec` and `:execrows` | Scans the table, and writes the new row in place of each row whose condition holds | The lookup argument for writes, and `Pg.applyUpdates` in the IR |
| `UPDATE … FROM` | Joins the target with the other tables, as a `SELECT` does | Nothing new beyond the two rows above |
| `WITH` whose parts are `SELECT` or `UPDATE` | Runs every part on the snapshot from before the statement, then writes the updates in order | The snapshot, and the rule that refuses stale reads, which stays a check of the translator |
| Enum labels in a `SET` and a `COALESCE` | Gives a string literal the type of its column or of the other argument | The type of a string literal in the interpreter |

## Gaps that the string translation has

The proved path refuses these, so they are left only where the string
translation writes code. Each one becomes a fix of the string translation
or a refusal before that translation is deleted.

- Arithmetic on `integer` and `smallint` checks the range of a `bigint`, so
  the printed code misses an overflow that PostgreSQL raises.
- A cast that narrows an integer, such as `x::integer` on a `bigint`, prints
  as `x` with no check of the range.
- `IS NULL` on an expression that cannot be NULL prints as a constant, so
  the printed code misses an error that the expression raises.
- `jsonb` equality compares text, but PostgreSQL compares the values.

## The printer link

`translate_sound` stops at the IR. The printed Lean code reads typed rows
from tables of the form `Key → Option Row`, but the IR's evaluator reads
lists of untyped values. A certificate for each query can close that gap,
as TypeScript's certificates do. It needs two hypotheses about the
database. The first is `Valid`, which says that each row sits under its own
key. That fact makes `Pg.lookup` give the rows that the IR's lookup gives.
The second says that each argument fits its type, such as the range of a
`bigint`.

## Tests of the interpreter

The interpreter is now the specification of the subset, so it needs a
check against the server. `tests/sql/pgcheck` already runs each scenario on
PostgreSQL. It can also run the interpreter on the same database and
compare the results.
