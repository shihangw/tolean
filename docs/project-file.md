# The project file

A project lists what to translate in `tolean.json`, at its root. Then
`tolean translate` builds every unit, and `tolean translate --check` writes
nothing and fails when a generated file is not current, which is the check
that CI runs.

```json
{
  "typescript": {
    "target": "ES2024",
    "sources": ["src/**/*.ts"],
    "overrides": [{ "sources": ["src/sensor/raise.ts"], "certify": true }]
  },
  "go": {
    "erasePackages": ["time"],
    "sources": ["ledger/*.go"],
    "overrides": [{ "sources": ["ledger/*.go"], "eraseTypes": ["Log"] }]
  },
  "sql": {
    "migrations": ["db/migrations/*.up.sql"],
    "sources": ["db/queries.sql"]
  }
}
```

Each language has an object. Its settings apply to every source, and each
entry in `overrides` changes them for the files that its own `sources` match.
Overrides apply in order, so the last value wins. In a glob, `*` matches
within one directory and `**` matches any number of directories.

Each language translates a different unit. A TypeScript file is one unit. A
Go package is one unit, so tolean groups the matched Go files by directory.
A SQL query file is one unit, which tolean translates against the
migrations, in sorted order. The defaults keep most entries short:

- The output goes next to the source: `src/sensor/raise.ts` gives
  `src/sensor/Raise.lean`, the package in `ledger/` gives `ledger/Ledger.lean`,
  and `db/queries.sql` gives `db/Queries.lean`. The namespace follows the
  path, such as `src.sensor.Raise`. An override can set `output` and
  `namespace` for one unit.
- The TypeScript target is ES2024, and `certify` is off. With `certify` on, a
  file that cannot have a certificate makes `tolean translate` fail with the
  reason.
- Lean module names start at the directory of `tolean.json`, so
  `src/sensor/Raise.lean` is the module `src.sensor.Raise`. When the Lean
  package's module names start elsewhere, set `moduleRoot` to that directory,
  relative to `tolean.json`. An import and a certificate name the module. A
  path component that Lean does not read as a name, such as `my-lib`, is
  written `«my-lib»`.
- A Go package starts from its exported functions, unless `roots` names
  others.
- A SQL file translates each query that it names, unless `queries` lists
  some of them.

A script that does not want a file can pass the same JSON inline, as in
`tolean translate --config '{"go":{"sources":["sorting/*.go"]}}'`. Paths in
the config are relative to the directory that Tolean runs in.

The single-file commands still work, but they are not a stable interface,
and their arguments can change between versions. Use `tolean.json` in your
project and in CI.
