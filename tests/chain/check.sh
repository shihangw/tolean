#!/usr/bin/env bash
# Checks `tolean chain` on the gauge project: the chain holds as committed, and
# `chain check` fails on a changed source, a missing project check and a claim
# whose proof has another type, and an obligation whose proof depends on a
# forbidden axiom.
# Run from tests/chain inside `nix develop`,
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

# Every generated file is current: tolean.json rebuilds exactly what is
# committed, the certificate included.
$T translate --check >/dev/null || fail "a generated file is not current: $($T translate --check 2>&1)"
echo "ok: generated files current"

# The manifest's hash is SHA-256 as shasum computes it.
want=$(shasum -a 256 sensor/raise.ts | cut -d' ' -f1)
grep -qF "\"sha256\": \"$want\"" sensor/Raise.lean.chain.json || fail "SHA-256 differs from shasum"
echo "ok: sha256"

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
$T translate --check >/dev/null 2>&1 && fail "translate --check accepted a changed source"
echo "ok: translate --check sees the change"
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

# Obligations use a fixed axiom policy rather than a project allowlist.
node --input-type=module - <<'JS'
import fs from "node:fs";
const path = "tolean.chain.json";
const project = JSON.parse(fs.readFileSync(path, "utf8"));
const {spec, proof, module} = project.claims[0];
project.obligations = [{spec, proof, module}];
fs.writeFileSync(path, JSON.stringify(project));
JS
check >/dev/null || fail "a proved obligation was rejected"
echo "ok: project proof of an obligation"
node --input-type=module - <<'JS'
import fs from "node:fs";
const path = "tolean.chain.json";
const project = JSON.parse(fs.readFileSync(path, "utf8"));
project.obligations[0].spec = "Spec.raise_other";
fs.writeFileSync(path, JSON.stringify(project));
JS
expect_fail "wrong obligation" "is not exactly Spec.raise_other"
node --input-type=module - <<'JS'
import fs from "node:fs";
const path = "tolean.chain.json";
const project = JSON.parse(fs.readFileSync(path, "utf8"));
project.obligations[0].proof = "Spec.raise_stays_under_max";
fs.writeFileSync(path, JSON.stringify(project));
JS
expect_fail "definition instead of proof" "is not a theorem"
node --input-type=module - <<'JS'
import fs from "node:fs";
const path = "tolean.chain.json";
const project = JSON.parse(fs.readFileSync(path, "utf8"));
project.obligations[0].proof = "propext";
project.obligations[0].axioms = ["propext"];
fs.writeFileSync(path, JSON.stringify(project));
JS
expect_fail "axiom instead of proof" "propext is not a theorem"
cp "$tmp/project.json" tolean.chain.json

# Compile adversarial proofs only in this temporary module, outside the
# warning-as-error build. Each theorem has exactly its obligation's type.
cat > "$tmp/ObligationAxioms.lean" <<'LEAN'
def obligationSpec : Prop := False
axiom forbidden : obligationSpec
theorem indirect : obligationSpec := forbidden
theorem supplied : obligationSpec := indirect
theorem admitted : obligationSpec := by sorry

def validSpec : Prop := True
theorem valid : validSpec := True.intro
LEAN
lake env lean --root="$tmp" -o "$tmp/ObligationAxioms.olean" "$tmp/ObligationAxioms.lean"
(
  export LEAN_PATH="$tmp"
  obligation_manifest() {
    node --input-type=module - "$@" <<'JS'
import fs from "node:fs";
const [spec, proof, ...axioms] = process.argv.slice(2);
const obligation = {spec, proof, module: "ObligationAxioms"};
if (axioms.length) obligation.axioms = axioms;
fs.writeFileSync("tolean.chain.json", JSON.stringify({
  files: [], obligations: [obligation]
}));
JS
  }
  obligation_manifest obligationSpec supplied
  expect_fail "transitive forbidden axiom" "supplied also depends on forbidden"
  obligation_manifest obligationSpec supplied forbidden
  expect_fail "obligation cannot widen axiom policy" "supplied also depends on forbidden"
  obligation_manifest obligationSpec admitted
  expect_fail "admitted obligation" "admitted also depends on sorryAx"
  obligation_manifest validSpec valid
  check >/dev/null || fail "a valid obligations-only chain was rejected: $(check)"
  echo "ok: valid obligations-only chain"
)
cp "$tmp/project.json" tolean.chain.json

trust=$($T chain trust tolean.chain.json raise_stays_under_max)
for want in "trusted: sensor.Raise:runtime" "trusted: callers" "tested: sensor.Raise:parser" "trusted: sensor.Raise:semantics"; do
  grep -qF "$want" <<<"$trust" || fail "chain trust lacks '$want'"
done
if grep -q "sensor.Raise:translator" <<<"$trust"; then fail "chain trust still lists the certified translator"; fi
echo "ok: trust"
$T chain graph tolean.chain.json | grep -q '"callers" -> "raise_stays_under_max"' || fail "graph lacks an edge"
echo "ok: graph"
