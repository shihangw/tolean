/**
 * Join the Lean files of one example into a single file that imports only
 * `Init`, for a Lean that runs in the browser and has no tolean `.olean` files.
 * The page builds the same file with the same function, from `site/src/lean.ts`.
 *
 *   node playground/bundle.ts <example dir> > Bundle.lean
 */
import { readFileSync, readdirSync } from 'node:fs';
import path from 'node:path';

import { type WorkspaceFile, bundle, claims, isProof, isSpec } from './site/src/lean.ts';

/** The Go Spec that generated Go code imports. */
export const goSpecPath = path.join(import.meta.dirname, '..', 'tolean/Go/Spec/Basic.lean');

const filesIn = (exampleDir: string, dir: string, keep: (f: string) => boolean): WorkspaceFile[] =>
  readdirSync(path.join(exampleDir, dir))
    .filter(keep)
    .sort()
    .map((f) => ({ path: `${dir}/${f}`, text: readFileSync(path.join(exampleDir, dir, f), 'utf8') }));

/** The files of an example: its sources and generated Lean, then its theorems. */
export function exampleFiles(exampleDir: string): { src: WorkspaceFile[]; theorems: WorkspaceFile[] } {
  const src = filesIn(exampleDir, 'src', (f) => !f.endsWith('.chain.json'));
  const theorems = filesIn(exampleDir, 'theorems', (f) => f.endsWith('.lean'));
  return { src, theorems };
}

/** The example's Lean files in import order: generated code, claims, proofs. */
export function leanInOrder(files: readonly WorkspaceFile[]): WorkspaceFile[] {
  const generated = files.filter((f) => f.path.startsWith('src/') && f.path.endsWith('.lean'));
  return [...generated, ...files.filter(isSpec), ...files.filter(isProof)];
}

if (process.argv[1] === import.meta.filename) {
  const exampleDir = process.argv[2];
  if (exampleDir == null) {
    process.stderr.write('usage: node playground/bundle.ts <example dir>\n');
    process.exit(2);
  }
  const { src, theorems } = exampleFiles(exampleDir);
  const files = [...src, ...theorems];
  const names = claims(files).map((c) => c.name);
  process.stdout.write(bundle(readFileSync(goSpecPath, 'utf8'), leanInOrder(files), names).text);
}
