#!/usr/bin/env bash
# Run from tests/typescript, after the root build.
set -euo pipefail
cd "$(dirname "$0")"
root=$(cd ../.. && pwd)
T="$root/.lake/build/bin/tolean"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
lean_path="$(cd "$root" && lake env printenv LEAN_PATH):$work"
cp corpus/obligations/squares.ts "$work/Input.ts"
cp corpus/obligations/Proof.lean "$work/Proof.lean"
compile() {
  (cd "$root" && LEAN_PATH="$lean_path" lake env lean --root="$work" \
    -o "$work/$1.olean" "$work/$1.lean")
}
certify() {
  (cd "$work" && "$T" certify Input.ts Out Out OutCert.lean OutCert \
    --proof-manifest chain.json --manifest Out.lean.chain.json)
}
check() {
  (cd "$root" && LEAN_PATH="$lean_path" lake env "$T" chain check "$work/chain.json")
}
manifest() {
  node --input-type=module - "$work/chain.json" "$1" <<'JS'
import fs from "node:fs";
const [path, proof] = process.argv.slice(2);
fs.writeFileSync(path, JSON.stringify({
  files: ["Out.lean.chain.json"],
  obligations: proof ? [{
    spec: "Out.sort obligation at 2:10",
    proof,
    module: proof.startsWith("Bad.") ? "Bad" : "Proof",
  }] : [],
}));
JS
}
fail() { echo "FAIL: $*" >&2; exit 1; }
expect_failure() {
  local expected=$1; shift
  if "$@" >"$work/failure.log" 2>&1; then fail "unexpected success: $*"; fi
  cat "$work/failure.log"
  grep -qF "$expected" "$work/failure.log" || fail "missing diagnostic: $expected"
}
(cd "$work" && "$T" translate Input.ts Out.lean Out)
compile Out
compile Proof
manifest ""
expect_failure "missing project proof" certify
manifest ProjectProof.wrong
certify
expect_failure "True" compile OutCert
manifest ProjectProof.squares
certify
compile OutCert
check

# This deliberately invalid fixture exists only in the temporary project.
# No production module declares or assumes an axiom.
cat >"$work/Bad.lean" <<'LEAN'
import Out
theorem Bad.proof : Out.«sort obligation at 2:10» := sorryAx _ true
LEAN
compile Bad
manifest Bad.proof
certify
compile OutCert
expect_failure "sorryAx" check
echo "ok: generated comparator obligations and project proofs"
