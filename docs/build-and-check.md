# Build and check

[Repository layout](repository-layout.md) describes where each part
of Tolean lives and how to add a language.

```sh
nix develop                                 # Lean 4.30.0, Node 24, pnpm 10
lake build --wfail                          # the library and .lake/build/bin/tolean
lake env leanchecker tolean                 # the kernel checks every built declaration again
.lake/build/bin/tolean parse file.ts        # print the syntax tree, or file:line:col: reason
.lake/build/bin/tolean translate file.ts File.lean My.Namespace
nix develop .#wasm -c wasm/build.sh         # the translator as WebAssembly, for playground/
cd tests/typescript && pnpm install
node check.ts                               # the Lean parser against tsc (see the language docs)
node checkTranslate.ts                      # the translator on the corpus and on random programs
pnpm test                                   # JS number laws and bigint division against the engine
cd ../../npm && pnpm install && pnpm build && TOLEAN_BINARY=$PWD/../.lake/build/bin/tolean pnpm test
cd ../tests/go && go run ./check            # the Lean Go parser against go/parser (see the language docs)
cd ../sql && go run ./pgcheck corpus        # the SQL translator against PostgreSQL (see the language docs)
(cd ../typescript && ./checkCertify.sh)     # per-file certificates for the corpus (see the TypeScript page)
cd ../chain && ./check.sh                   # chain manifests on a sample project (see verification-chain.md)
cd ../../docs && pnpm install && pnpm build # the docs site, which fails on a dead link
```

CI runs all of these on each push and pull request, in the same Nix dev
shell, from `.github/workflows/ci.yml`. It also runs the number laws on
every maintained Node release line (`nix run .#test-engines`), and it fails
if a check leaves a committed file changed.

CI runs in stages, so a failure stops the expensive work early. The `check`
job runs `lake build --wfail` and the checks above, on each pull request.
The `docs` job builds the docs site on each pull request too, and it needs
no Lean, so it finishes first.
On `main`, when `check` passes, `wasm` builds the playground's WebAssembly
translator and requires that it gives the native result, and `pages` then
publishes the playground, with the docs site under `/docs/`. Pull requests skip the WebAssembly build, because
only the published page needs it. To run it for a branch, start `ci` by
hand from the Actions tab.

The npm release is `.github/workflows/release.yml`. To release, raise the
version in `npm/package.json` and `tolean/Version.lean`, and merge that to
main. When CI passes on main and npm does not have that version yet, CI's
last job starts the release. The release builds the native `tolean` on
Linux, macOS and Windows, packs the npm packages, and installs them as a
user would. Then it waits for approval, publishes the packages to npm and
tags the commit. While a release is queued, waiting or running, CI starts
no other. So a later push starts one only when the release failed or you
rejected it.

The release also runs by hand from the Actions tab. By default that is a
dry run that uploads the packages. With `publish` set, it publishes as
above. Use that to finish a release that failed partway.
