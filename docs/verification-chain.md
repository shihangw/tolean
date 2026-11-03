# The verification chain

What Tolean produces is a verification chain: a path from the source code
that runs to theorems about it, where every link is proved, tested against a
reference, or trusted. The graphs show the chain for each language, and which
links are which:

- [TypeScript](typescript/verification.svg)
- [Go](go/verification.svg)
- [PostgreSQL](postgresql/verification.svg)

Each language also splits into nested subsets: what the parser reads, what
the translator accepts, and what is proved. [This chart](subsets.svg)
lists them.

## Chain manifests

The chain is also data. Each translation writes `<output>.chain.json` next to
the Lean file. It records the Tolean version, the SHA-256 of each source file
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
Tolean's own checks, which hold for the Tolean version that wrote the
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
status; [this is the graph](chain-gauge.svg) of the sample project in
`tests/chain`, which `tests/chain/check.sh` checks.

To set up Tolean in your own project, read
[Using Tolean in a project](project-layout.md). It shows the folder
layout and a full example for each language, and
[the project file](project-file.md) lists every setting of `tolean.json`.
