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

Lean does not run in the page yet, so the page marks every claim as not
checked. CI checks each example instead: it runs `tolean translate --check`
and `lake build --wfail` in every directory under `examples/`.

The plan is to run Lean in the browser, compiled to WebAssembly. That Lean
cannot load Tolean's `.olean` files, because they must come from the same
Lean commit. So the page joins the files of a workspace into one Lean file
that imports only `Init`, with `bundle()` in `site/src/lean.ts`. To see that
file for an example, run:

```sh
node playground/bundle.ts playground/examples/sort > Bundle.lean
lean Bundle.lean
```

The bundle checks each claim in place of `#audit_claims`, which needs
`import Lean`. The line `example : Spec.c := Proof.c` fails unless the
theorem has exactly the claim's type, and `#print axioms` lists what the
theorem relies on. A claim whose axioms include `sorryAx` relies on a step
that failed, so the page will mark it as broken.

The threaded Lean needs the page to be cross-origin isolated. GitHub Pages
cannot send the headers for that, so `coi-serviceworker` adds them in the
browser.

## Build

```sh
cd playground/site
pnpm install
pnpm dev      # serve on localhost:5173
pnpm build    # write the static site to dist/
```

To add an example, create a directory under `examples/` with a `tolean.json`,
a `src/` folder, a `theorems/` folder and a `lakefile.toml`, like
`examples/sort`.
