#!/usr/bin/env bash
# Checks `tolean chain` on the gauge project: the chain holds as committed, and
# `chain check` fails on a changed source, a missing project check and a claim
# whose proof has another type. Run from tests/chain inside `nix develop`,
# after `lake build` at the root.
set -euo pipefail
cd "$(dirname "$0")"
T=../../.lake/build/bin/tolean
tmp=$(mktemp -d)
trap 'cp "$tmp/raise.ts" sensor/raise.ts; cp "$tmp/project.json" tolean.chain.json; [ -f "$tmp/Raise.lean.good" ] && cp "$tmp/Raise.lean.good" sensor/Raise.lean; rm -rf "$tmp"' EXIT
cp sensor/raise.ts "$tmp/raise.ts"
cp tolean.chain.json "$tmp/project.json"

fail() { echo "FAIL: $*"; exit 1; }
check() { lake env "$T" chain check tolean.chain.json "$@" 2>&1; }
expect_fail() { # <name> <expected text> [args]
  local name=$1 want=$2; shift 2
  if out=$(check "$@"); then fail "$name: chain check passed"; fi
  grep -qF "$want" <<<"$out" || fail "$name: expected '$want', got: $out"
  echo "ok: $name"
}

# The generated file is current, and its hash is SHA-256 as shasum computes it.
$T translate sensor/raise.ts "$tmp/Raise.lean" sensor.Raise
cmp -s "$tmp/Raise.lean" sensor/Raise.lean || fail "sensor/Raise.lean is not current"
want=$(shasum -a 256 sensor/raise.ts | cut -d' ' -f1)
grep -qF "\"sha256\": \"$want\"" sensor/Raise.lean.chain.json || fail "SHA-256 differs from shasum"
echo "ok: sha256"

# The certificate is current: tolean certify writes the committed file.
$T certify sensor/raise.ts sensor.Raise sensor.Raise "$tmp/RaiseCert.lean" sensor.RaiseCert
cmp -s "$tmp/RaiseCert.lean" sensor/RaiseCert.lean || fail "sensor/RaiseCert.lean is not current"
echo "ok: certificate current"

lake build --wfail >/dev/null

# A wrong translation breaks the certificate: add 1 to one branch.
cp sensor/Raise.lean "$tmp/Raise.lean.good"
sed -i.bak 's/level := (g.level + step)/level := (g.level + step + 1)/' sensor/Raise.lean
rm -f sensor/Raise.lean.bak
grep -q 'step + 1' sensor/Raise.lean || fail "the mutation did not apply"
lake build sensor.Raise >/dev/null
if lake env lean sensor/RaiseCert.lean >/dev/null 2>&1; then
  cp "$tmp/Raise.lean.good" sensor/Raise.lean
  fail "the certificate accepted a wrong translation"
fi
cp "$tmp/Raise.lean.good" sensor/Raise.lean
lake build --wfail >/dev/null
echo "ok: a wrong translation breaks the certificate"
check >/dev/null || fail "the committed chain does not hold: $(check)"
echo "ok: the chain holds"

echo "// edit" >> sensor/raise.ts
expect_fail "changed source" "sensor/raise.ts changed since it was translated"
cp "$tmp/raise.ts" sensor/raise.ts

sed -i.bak 's/"status": "trusted"/"status": "tested", "evidence": {"check": "caller-audit", "by": "project"}/' tolean.chain.json
expect_fail "missing project check" "check caller-audit did not pass"
check --passed caller-audit >/dev/null || fail "--passed caller-audit: chain check failed"
echo "ok: --passed"
cp "$tmp/project.json" tolean.chain.json

sed -i.bak 's/"spec": "Spec.raise_stays_under_max"/"spec": "Spec.raise_other"/' tolean.chain.json
expect_fail "wrong spec" "is not exactly Spec.raise_other"
cp "$tmp/project.json" tolean.chain.json
rm -f tolean.chain.json.bak

trust=$($T chain trust tolean.chain.json raise_stays_under_max)
for want in "trusted: sensor.Raise:runtime" "trusted: callers" "tested: sensor.Raise:parser" "trusted: sensor.Raise:semantics"; do
  grep -qF "$want" <<<"$trust" || fail "chain trust lacks '$want'"
done
if grep -q "sensor.Raise:translator" <<<"$trust"; then fail "chain trust still lists the certified translator"; fi
echo "ok: trust"
$T chain graph tolean.chain.json | grep -q '"callers" -> "raise_stays_under_max"' || fail "graph lacks an edge"
echo "ok: graph"
