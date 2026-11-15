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
if [[ -n "${TOLEAN_CERTIFY_WORK:-}" ]]; then
  # Keep every generated Lean file and diagnostic in this caller-owned directory.
  export work=$TOLEAN_CERTIFY_WORK
  mkdir -p "$work"
else
  export work=$(mktemp -d)
  trap 'rm -rf "$work"' EXIT
fi
mkdir -p "$work/Corpus" "$work/results" "$work/logs"
export lean_path="$(cd "$root" && lake env printenv LEAN_PATH):$work"

# Certify one file. The result is in $work/results/<name>: proved, skipped, or
# failed followed by Lean's output.
certifyOne() {
  local f=$1 b n result translate_log certify_log output_log cert_log rc required=false
  b=$(basename "$f" .ts)
  n="$(tr '[:lower:]' '[:upper:]' <<<"${b:0:1}")${b:1}"
  result="$work/results/$b"
  if grep -qx '// certify: required' "$f"; then required=true; fi
  translate_log="$work/logs/$b.translate.log"
  certify_log="$work/logs/$b.certify.log"
  output_log="$work/logs/$b.output-compile.log"
  cert_log="$work/logs/$b.certificate-compile.log"
  if ! $T translate "$f" "$work/Corpus/$n.lean" "Corpus.$n" >"$translate_log" 2>&1; then
    if [[ "$required" == true ]]; then
      {
        echo failed
        echo "A required certificate translation was refused"
        cat "$translate_log"
      } >"$result"
      return 0
    fi
    case "$b" in
      localFunctionCertificate | localFunctionNumber | localFunctionLoopCertificates | \
      localFunctionReturnsAndChanges | localFunctionSiblingCalls | \
      localFunctions | localArrows | localFunctionOwnedArray | localFunctionLoopParameter)
        {
          echo failed
          echo "A required local-function translation was refused"
          cat "$translate_log"
        } >"$result"
        return 0
        ;;
    esac
    echo skipped >"$result"
    return 0
  fi
  if ! $T certify "$f" "Corpus.$n" "Corpus.$n" "$work/Corpus/${n}Cert.lean" "Corpus.${n}Cert" \
      >"$certify_log" 2>&1; then
    if [[ "$required" == true ]]; then
      {
        echo failed
        echo "A required certificate was refused"
        cat "$certify_log"
      } >"$result"
      return 0
    fi
    case "$b" in
      localFunctionCertificate | localFunctionNumber | localFunctionLoopCertificates | \
      localFunctionReturnsAndChanges | localFunctionSiblingCalls | \
      localFunctions | localArrows | localFunctionOwnedArray | localFunctionLoopParameter)
        {
          echo failed
          echo "A required local-function certificate was refused"
          cat "$certify_log"
        } >"$result"
        return 0
        ;;
    esac
    echo skipped >"$result"
    return 0
  fi
  if ! (cd "$root" && LEAN_PATH=$lean_path lake env lean --root="$work" \
      -o "$work/Corpus/$n.olean" "$work/Corpus/$n.lean" >"$output_log" 2>&1); then
    {
      echo failed
      echo "Lean refused the translated output"
      cat "$output_log"
    } >"$result"
    return 0
  fi
  rc=0
  (cd "$root" && LEAN_PATH=$lean_path lake env lean "$work/Corpus/${n}Cert.lean" \
    >"$cert_log" 2>&1) || rc=$?
  if [[ "$rc" -eq 0 ]] && ! grep -q "error" "$cert_log"; then
    echo proved >"$result"
  else
    {
      echo failed
      echo "Lean refused the complete certificate"
      cat "$cert_log"
    } >"$result"
  fi
}
export -f certifyOne

# SHARD=k/n certifies only the k-th of n equal parts of the corpus, so that
# CI can spread the files over several machines. Without SHARD, the script
# certifies every file.
shard=${SHARD:-1/1}
k=${shard%/*} n=${shard#*/}
jobs=$(nproc 2>/dev/null || sysctl -n hw.ncpu)
ls corpus/translate/accept/*.ts | awk -v k="$k" -v n="$n" '(NR - 1) % n == k - 1' |
  xargs -P "$jobs" -I {} bash -c 'certifyOne "$1"' _ {}

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
echo "certify: $proved files proved, $skipped files without a certificate (not translated, or not certifiable yet)"
[ "$failed" -eq 0 ] || exit 1
[ "$proved" -gt 0 ] || { echo "FAIL: no file was certified"; exit 1; }
