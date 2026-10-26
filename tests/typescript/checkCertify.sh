#!/usr/bin/env bash
# Certifies each file in corpus/translate that tolean can certify, and requires
# Lean to accept every certificate. Run from tests/typescript inside
# `nix develop`, after `lake build` at the root.
set -euo pipefail
cd "$(dirname "$0")"
T=../../.lake/build/bin/tolean
root=$(cd ../.. && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/Corpus"
lean_path="$(cd "$root" && lake env printenv LEAN_PATH):$work"
proved=0 skipped=0
for f in corpus/translate/*.ts; do
  b=$(basename "$f" .ts)
  n="$(tr '[:lower:]' '[:upper:]' <<<"${b:0:1}")${b:1}"
  $T translate "$f" "$work/Corpus/$n.lean" "Corpus.$n" 2>/dev/null || { skipped=$((skipped + 1)); continue; }
  $T certify "$f" "Corpus.$n" "Corpus.$n" "$work/Corpus/${n}Cert.lean" "Corpus.${n}Cert" 2>/dev/null ||
    { skipped=$((skipped + 1)); continue; }
  (cd "$root" && LEAN_PATH=$lean_path lake env lean --root="$work" -o "$work/Corpus/$n.olean" "$work/Corpus/$n.lean" >/dev/null)
  if ! out=$(cd "$root" && LEAN_PATH=$lean_path lake env lean "$work/Corpus/${n}Cert.lean" 2>&1) ||
      grep -q "error" <<<"$out"; then
    echo "FAIL $b: Lean refused the certificate"
    echo "$out" | head -20
    exit 1
  fi
  proved=$((proved + 1))
done
echo "certify: $proved files proved, $skipped files without a certificate yet (loops, number, or not translated)"
[ "$proved" -gt 0 ] || { echo "FAIL: no file was certified"; exit 1; }
