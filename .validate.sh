#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"

nix develop --command lake build tolean.TypeScript.IR.Eval
nix develop --command lake build tolean.TypeScript.Proof.Expr
nix develop --command lake build tolean.TypeScript.Spec.Coverage
nix develop --command lake build --wfail
nix develop --command bash -c \
  'cd tests/typescript && node check.ts && ./checkCertify.sh && node checkTranslate.ts && pnpm test'
