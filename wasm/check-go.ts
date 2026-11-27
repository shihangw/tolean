/**
 * Require the Go corpus to produce the same Lean in native and WASM builds.
 * Run from the repository root after wasm/build.sh: node wasm/check-go.ts.
 */
import { deepStrictEqual, strictEqual } from 'node:assert';
import { spawnSync } from 'node:child_process';
import { readdirSync, readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { translateWorkspaceInWasm } from '../tests/typescript/wasm.ts';

const root = new URL('../', import.meta.url);
const corpus = new URL('tests/go/corpus/translate/', root);
const tolean = process.env.TOLEAN ?? fileURLToPath(new URL('.lake/build/bin/tolean', root));
let checked = 0;
for (const name of readdirSync(corpus)) {
  const dir = new URL(`${name}/`, corpus);
  const [namespace, ...args] = readFileSync(new URL('args', dir), 'utf8').trim().split(/\s+/);
  const options: Record<string, string[]> = { roots: [], eraseTypes: [], erasePackages: [] };
  const keys: Record<string, string> = {
    '--root': 'roots', '--erase-type': 'eraseTypes', '--erase-package': 'erasePackages',
  };
  for (let i = 0; i < args.length; i += 2) {
    const key = keys[args[i]];
    if (key === undefined || args[i + 1] === undefined) {
      throw new Error(`${name}/args: unsupported option ${args[i]}`);
    }
    options[key].push(args[i + 1]);
  }
  const output = `${namespace}.lean`;
  const prefix = `corpus/translate/${name}/`;
  const files = [
    {
      path: 'tolean.json',
      text: JSON.stringify({ go: { sources: [`${prefix}*.go`], output, namespace, ...options } }),
    },
    ...readdirSync(dir).filter((p) => p.endsWith('.go')).map((path) => ({
      path: prefix + path, text: readFileSync(new URL(path, dir), 'utf8'),
    })),
  ];
  const run = spawnSync(tolean, ['translate-workspace'], {
    input: JSON.stringify({ files }), encoding: 'utf8',
  });
  if (run.error !== undefined) throw run.error;
  strictEqual(run.status, 0, `${name}: native workspace translation failed: ${run.stderr}`);
  const native = JSON.parse(run.stdout);
  strictEqual(native.error, undefined, `${name}: native workspace error`);
  strictEqual(native.units?.length, 1, `${name}: expected one translated package`);
  strictEqual(native.units[0].error, undefined, `${name}: native translation refused`);
  strictEqual(native.units[0].lean, readFileSync(new URL(output, dir), 'utf8'),
    `${name}: native Lean differs from the corpus`);
  deepStrictEqual(translateWorkspaceInWasm(files), native,
    `${name}: WASM workspace output differs from native`);
  checked++;
}
console.log(`Go WASM translation: ${checked} packages match native and the corpus`);
