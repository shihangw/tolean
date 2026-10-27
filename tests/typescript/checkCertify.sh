#!/usr/bin/env bash
# Certifies each file in corpus/translate that tolean can certify, and requires
# Lean to accept every certificate. Run from tests/typescript inside
# `nix develop`, after `lake build` at the root.
#
# The files are independent, so they run in parallel, one job for each CPU.
set -euo pipefail
cd "$(dirname "$0")"
export T=$PWD/../../.lake/build/bin/tolean
export root=$(cd ../.. && pwd)
export work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/Corpus" "$work/results"
export lean_path="$(cd "$root" && lake env printenv LEAN_PATH):$work"

# Certify one file. The result is in $work/results/<name>: proved, skipped, or
# failed followed by Lean's output.
certifyOne() {
  local f=$1 b n out result
  b=$(basename "$f" .ts)
  n="$(tr '[:lower:]' '[:upper:]' <<<"${b:0:1}")${b:1}"
  result="$work/results/$b"
  if ! $T translate "$f" "$work/Corpus/$n.lean" "Corpus.$n" 2>/dev/null ||
      ! $T certify "$f" "Corpus.$n" "Corpus.$n" "$work/Corpus/${n}Cert.lean" "Corpus.${n}Cert" 2>/dev/null; then
    echo skipped >"$result"
    return 0
  fi
  (cd "$root" && LEAN_PATH=$lean_path lake env lean --root="$work" -o "$work/Corpus/$n.olean" "$work/Corpus/$n.lean" >/dev/null)
  if out=$(cd "$root" && LEAN_PATH=$lean_path lake env lean "$work/Corpus/${n}Cert.lean" 2>&1) &&
      ! grep -q "error" <<<"$out"; then
    echo proved >"$result"
  else
    { echo failed; echo "$out" | head -20; } >"$result"
  fi
}
export -f certifyOne

jobs=$(nproc 2>/dev/null || sysctl -n hw.ncpu)
ls corpus/translate/accept/*.ts | xargs -P "$jobs" -I {} bash -c 'certifyOne "$1"' _ {}

proved=0 skipped=0 failed=0
for result in "$work"/results/*; do
  case $(head -1 "$result") in
    proved) proved=$((proved + 1)) ;;
    skipped) skipped=$((skipped + 1)) ;;
    *)
      failed=$((failed + 1))
      echo "FAIL $(basename "$result"): Lean refused the certificate"
      tail -n +2 "$result"
      ;;
  esac
done
echo "certify: $proved files proved, $skipped files without a certificate (not translated)"
[ "$failed" -eq 0 ] || exit 1
[ "$proved" -gt 0 ] || { echo "FAIL: no file was certified"; exit 1; }
