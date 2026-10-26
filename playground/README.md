# Playground

The playground is a static page where you read and edit Tolean examples. It
is built with React and Vite, and `.github/workflows/pages.yml` publishes it
to GitHub Pages.

Each workspace has two folders. `src/` holds the source code and the Lean
that Tolean generates from it. `theorems/` holds the claims in `*.spec.lean`
files, and next to each one, the proofs in a `*.proof.lean` file. The page
shows the claims first, because a person must read them. Each proof is
folded under its claim, and the helper lemmas sit in their own group.

## What runs where

Lean runs in the page, compiled to WebAssembly, and checks the proofs as you
edit. The build is not ours: it comes from
[cauli/lean4-wasm-in-browser](https://github.com/cauli/lean4-wasm-in-browser)
(Apache-2.0), which runs a fork of Lean. `site/lean-runtime.json` pins its
release by SHA-256, and `site/scripts/lean-runtime.ts` downloads it, checks
it and writes `site/public/lean/`. The page downloads about 130 MB the first
time, and the browser keeps it after that.

That Lean cannot load Tolean's `.olean` files, because they must come from
the same Lean commit. So the page joins the files of a workspace into one
Lean file that imports only `Init`, with `bundle()` in `site/src/lean.ts`.
To see that file for an example, run:

```sh
node playground/bundle.ts playground/examples/sort > Bundle.lean
lean Bundle.lean
```

The bundle checks each claim in place of `#audit_claims`, which needs
`import Lean`. The line `example : Spec.c := Proof.c` fails unless the
theorem has exactly the claim's type, and `#print axioms` lists what the
theorem relies on. A claim whose axioms include `sorryAx` relies on a step
that failed, so the page marks it as broken and shows the first error.

Each check runs in a fresh worker. After a check that unfolds a recursive
definition, this Lean build fails every later check in the same worker, and
the generated code is full of recursive loop functions. So the page keeps
one spare worker that has already started Lean, and it starts the next
spare after each check. The bug is reported as
[cauli/lean4-wasm-in-browser#4](https://github.com/cauli/lean4-wasm-in-browser/issues/4).

CI checks each example twice. It runs `tolean translate --check` and
`lake build --wfail` with the pinned Lean, and `site/scripts/check-wasm.ts`
runs the bundle on the Lean that the page runs. The two Leans differ, so a
proof must pass on both.

The threaded Lean needs the page to be cross-origin isolated. GitHub Pages
cannot send the headers for that, so `coi-serviceworker` adds them in the
browser.

## Build

```sh
nix develop .#wasm -c wasm/build.sh   # the translator, from the repository root
cd playground/site
pnpm install
pnpm dev                       # serve on localhost:5173
pnpm build                     # write the static site to dist/
node scripts/check-wasm.ts     # check the examples on the page's Lean
```

To add an example, create a directory under `examples/` with a `tolean.json`,
a `src/` folder, a `theorems/` folder and a `lakefile.toml`, like
`examples/sort`.
