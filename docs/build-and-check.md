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

CI runs in stages. The `build` job runs `lake build --wfail` and saves
Lake's build output in the Actions cache. Then the checks above run in
three jobs at once, `typescript`, `certify` and `other`, which restore that
cache instead of building again. The certificate check is the slowest, so
`certify` splits the corpus over two machines with `SHARD=1/2` and
`SHARD=2/2`. The `check` job passes when all of them pass, and branch
protection requires it. The `docs` job builds the docs site on each pull
request too, and it needs no Lean, so it finishes first.
On `main`, `.github/workflows/wasm.yml` builds the playground's WebAssembly
translator next to the checks, after `build`, and requires that it gives
the native result. Then `pages` publishes the playground, with the docs site
under `/docs/`. Only the published page needs WebAssembly, so a pull request
runs the build only when it changes something that only the build uses:
`wasm/`, the playground site, `wasm.yml`, the `lean-build` action, the flake
or the Lean toolchain.
To run it for any branch, start `ci` by hand from the Actions tab, or run
`gh workflow run ci.yml --ref <branch>`.

GitHub keeps at most 10 GB of Actions caches for the repository, and above
that it evicts caches on its own. So at the end of each run, `prune-caches`
deletes the caches on that branch or pull request that no run will restore
again, and `cache-cleanup.yml` deletes a pull request's caches when it
closes. Only main saves the translator's WebAssembly build, which takes
about 300 MB.

The npm release is `.github/workflows/release.yml`. To release, raise the
version in `npm/package.json` and `tolean/Version.lean`, and merge that to
main. When CI passes on main and that version has no GitHub release yet,
CI's last job starts the release. The release builds the native `tolean` on
Linux, macOS and Windows, packs the npm packages, and installs them as a
user would. Then it waits for approval, publishes the packages to npm and
tags the commit. While a release is queued, waiting or running, CI starts
no other. So a later push starts one only when the release failed or you
rejected it.

To pause releases, for example while a known problem would break them, run
`gh workflow disable release.yml`, or disable the workflow from the Actions
tab. CI then starts no release, and the workflow cannot run by hand either.
`gh workflow enable release.yml` resumes releases, and the next push to main
starts one if npm still lacks the version.

The release also runs by hand from the Actions tab. By default that is a
dry run that uploads the packages. With `publish` set, it publishes as
above. Use that to finish a release that failed partway.
