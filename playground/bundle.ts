/**
 * Join the Lean files of one example into a single file that imports only
 * `Init`, for a Lean that runs in the browser and has no tolean `.olean` files.
 *
 *   node playground/bundle.ts <example dir> > Bundle.lean
 *
 * The files go in import order: the Go Spec, the generated code, the claims,
 * then the proofs. `#audit_claims` needs `import Lean`, so the bundle checks
 * each claim itself: `example : Spec.c := Proof.c` fails unless the theorem
 * has exactly the claim's type, and `#print axioms` lists what it relies on.
 */
import { readFileSync, readdirSync } from 'node:fs';
import path from 'node:path';

const exampleDir = process.argv[2];
if (exampleDir == null) {
  process.stderr.write('usage: node playground/bundle.ts <example dir>\n');
  process.exit(2);
}
const toleanRoot = path.join(import.meta.dirname, '..');

const theorems = path.join(exampleDir, 'theorems');
const leanIn = (dir: string, suffix: string) =>
  readdirSync(dir)
    .filter((f) => f.endsWith(suffix))
    .sort()
    .map((f) => path.join(dir, f));

const generated = leanIn(path.join(exampleDir, 'src'), '.lean');
const specs = leanIn(theorems, '.spec.lean');
const proofs = leanIn(theorems, '.proof.lean');
const files = [
  path.join(toleanRoot, 'tolean/Go/Spec/Basic.lean'),
  ...generated,
  ...specs,
  ...proofs,
];

const body = (file: string) =>
  readFileSync(file, 'utf8')
    .split('\n')
    .filter((line) => !line.startsWith('import ') && !line.startsWith('#audit_claims'))
    .join('\n');

const claims = specs.flatMap((file) =>
  [...readFileSync(file, 'utf8').matchAll(/^def (\S+) : Prop/gm)].map((m) => m[1]),
);

const parts = files.map((file) => `-- ${path.relative(exampleDir, file)}\n${body(file)}`);
const checks = claims.map(
  (c) => `example : Spec.${c} := Proof.${c}\n#print axioms Proof.${c}`,
);
process.stdout.write([...parts, '-- claim checks', ...checks].join('\n\n') + '\n');
