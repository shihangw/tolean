#!/usr/bin/env bash
set -euo pipefail
umask 077

readonly root=/tmp/step11-recursion
readonly branch=step-11-recursion
readonly base=49ec516ee30afe088faed90588e6fa0dd0c6026c
readonly source_head=264434ca24e489abcba9b59adbdae6591a00a77d
readonly source_tree=71a2a446f89e710b1fcd5e7ff42059f932b7d169
readonly receipt=/tmp/tolean-step11-validation-264434c.receipt
readonly helper_path="$(readlink -f "${BASH_SOURCE[0]}")"
readonly -a helpers=(
  "$helper_path"
  "$root/flake.lock"
  "$root/lean-toolchain"
  "$root/tolean/TypeScript/Edition.lean"
  "$root/docs/decisions/2026-11-17-recursion-certificates.md"
  "$root/docs/plans/pure-typescript.md"
  "$root/docs/typescript/README.md"
  "$root/docs/package.json"
  "$root/docs/pnpm-lock.yaml"
  "$root/tests/typescript/check.ts"
  "$root/tests/typescript/checkCertify.sh"
  "$root/tests/typescript/checkTranslate.ts"
  "$root/tests/typescript/interpreter.test.ts"
  "$root/tests/typescript/corpus/certify/reject/recursiveFunction.ts"
  "$root/tests/typescript/corpus/certify/reject/recursiveInterface.ts"
  "$root/tests/typescript/corpus/translate/accept/structuralRecursion.ts"
  "$root/tests/typescript/package.json"
  "$root/tests/typescript/pnpm-lock.yaml"
)

exec 9>/tmp/tolean-long-validation.lock
flock -x 9
rm -f "$receipt" "$receipt.tmp"

fail() {
  printf 'STEP11_VALIDATION_FAIL: %s\n' "$*" >&2
  exit 1
}

helper_hashes() {
  sha256sum "${helpers[@]}"
}

check_pins_and_clean() {
  local current_source_head current_tree status committed_paths
  [[ "$(git -C "$root" branch --show-current)" == "$branch" ]] ||
    fail "worktree is not on $branch"
  [[ "$(git -C "$root" rev-parse origin/main)" == "$base" ]] ||
    fail "origin/main changed from the pinned base"
  current_source_head=$(git -C "$root" rev-parse HEAD^)
  [[ "$current_source_head" == "$source_head" ]] ||
    fail "the validation helper is not a commit on the pinned source head"
  current_tree=$(git -C "$root" rev-parse "$source_head^{tree}")
  [[ "$current_tree" == "$source_tree" ]] ||
    fail "the pinned source tree changed"
  git -C "$root" merge-base --is-ancestor "$base" "$source_head" ||
    fail "the pinned base is not an ancestor of the source head"
  [[ "$(git -C "$root" rev-list --count "$source_head..HEAD")" == 1 ]] ||
    fail "HEAD must contain only the validation-helper commit after source_head"
  committed_paths=$(git -C "$root" diff-tree --no-commit-id --name-only -r HEAD)
  [[ "$committed_paths" == ".validate.sh" ]] ||
    fail "the commit after source_head must add only .validate.sh"
  status=$(git -C "$root" status --porcelain --untracked-files=no)
  [[ -z "$status" ]] || fail "tracked files are dirty: $status"
  printf 'STEP11_PINS_OK base=%s source_head=%s tree=%s tracked_clean=yes\n' \
    "$base" "$source_head" "$source_tree"
}

check_pins_and_clean
readonly helper_hash_start="$(helper_hashes)"
printf 'START_SOURCE_HEAD=%s\nSTART_TREE=%s\nHELPER_HASHES_START:\n%s\n' \
  "$source_head" "$source_tree" "$helper_hash_start"

(
  cd "$root"
  nix develop --command lake build --wfail
  nix develop --command lake env leanchecker tolean
)

(
  cd "$root/tests/typescript"
  nix develop --command pnpm install --frozen-lockfile
  nix develop --command node check.ts
  nix develop --command node checkTranslate.ts
  nix develop --command pnpm test
  nix develop --command ./checkCertify.sh
)

(
  cd "$root/tests/chain"
  nix develop --command ./check.sh
)

(
  cd "$root"
  for example in playground/examples/*/; do
    (
      cd "$example"
      nix develop --command ../../../.lake/build/bin/tolean translate --check
      nix develop --command lake build --wfail
    )
  done
)

(
  cd "$root/docs"
  nix develop --command pnpm install --frozen-lockfile
  nix develop --command pnpm build
)

(
  cd "$root"
  git diff --exit-code
)

check_pins_and_clean
readonly helper_hash_end="$(helper_hashes)"
[[ "$helper_hash_start" == "$helper_hash_end" ]] ||
  fail "validation helpers changed during the run"

{
  printf 'STEP11_VALIDATION_PASSED\n'
  printf 'BASE=%s\nSOURCE_HEAD=%s\nTREE=%s\n' "$base" "$source_head" "$source_tree"
  printf 'VALIDATION_HEAD=%s\n' "$(git -C "$root" rev-parse HEAD)"
  printf 'TRACKED_CLEAN_BEFORE_AND_AFTER=yes\n'
  printf 'HELPER_HASHES_START:\n%s\nHELPER_HASHES_END:\n%s\n' \
    "$helper_hash_start" "$helper_hash_end"
  printf 'CHECKS=lake build --wfail; leanchecker; TypeScript parser, translator, interpreter, and certificate corpus; chain manifests; playground examples; docs build; generated-file diff\n'
} >"$receipt.tmp"
mv "$receipt.tmp" "$receipt"
printf 'STEP11_VALIDATION_RECEIPT=%s\n' "$receipt"
