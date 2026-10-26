/**
 * Check every example on the Lean that the page runs, in Node, and fail when
 * a claim is not proved there. CI checks the examples with the pinned Lean
 * too, but the page runs a newer Lean, and a proof can pass on one and fail on
 * the other. Run `node scripts/lean-runtime.ts` first.
 *
 * This boots lean.js the way the headless runner of
 * github.com/cauli/lean4-wasm-in-browser (Apache-2.0) does. Each example gets
 * its own process, because this Lean build can fail a second check.
 */
import { spawnSync } from 'node:child_process';
import { mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { createRequire } from 'node:module';
import path from 'node:path';
import vm from 'node:vm';

import { exampleFiles, goSpecPath, leanInOrder } from '../../bundle.ts';
import { bundle, claims } from '../src/lean.ts';
import { statuses } from '../src/checker.ts';

const site = path.join(import.meta.dirname, '..');
const leanDir = path.join(site, 'public/lean');

interface Diagnostic {
  severity: 'error' | 'warning' | 'information';
  pos?: { line: number; column: number };
  data: string;
}

/** Start Lean from lean.js, with the Init library on a real directory, and check one file. */
async function checkOne(code: string): Promise<Diagnostic[]> {
  const root = path.join(site, '.cache/node-lean');
  const lib = path.join(root, 'lib/lean');
  const index = JSON.parse(readFileSync(path.join(leanDir, 'init.index.json'), 'utf8')) as {
    path: string;
    offset: number;
    length: number;
  }[];
  const { gunzipSync } = await import('node:zlib');
  const pack = gunzipSync(readFileSync(path.join(leanDir, 'init.pack.bin')));
  for (const e of index) {
    const file = path.join(lib, e.path);
    mkdirSync(path.dirname(file), { recursive: true });
    writeFileSync(file, pack.subarray(e.offset, e.offset + e.length));
  }

  // Lean's threads load lean.js with require(), so it needs a CommonJS
  // package.json beside it; this site's package.json says "module".
  const bin = path.join(root, 'bin');
  mkdirSync(bin, { recursive: true });
  writeFileSync(path.join(bin, 'package.json'), '{ "type": "commonjs" }\n');
  writeFileSync(path.join(bin, 'lean.js'), readFileSync(path.join(leanDir, 'lean.js')));
  const leanJs = path.join(bin, 'lean.js');
  const diagnostics: Diagnostic[] = [];
  let capturing = false;
  const onLine = (text: string) => {
    if (!capturing || !text.startsWith('{')) return;
    try {
      const d = JSON.parse(text) as Diagnostic;
      if (typeof d.severity === 'string') diagnostics.push(d);
    } catch {
      // Not a diagnostic.
    }
  };
  // The glue reads its settings from a global `Module`.
  const Module: Record<string, unknown> & { [k: string]: any } = {
    noInitialRun: true,
    INITIAL_MEMORY: 2048 * 1024 * 1024,
    locateFile: (p: string) => path.join(leanDir, p),
    print: onLine,
    printErr: onLine,
  };
  const ready = new Promise<void>((resolve, reject) => {
    Module.preRun = [
      () => {
        const FS = Module.FS;
        let current = '';
        for (const part of root.split('/').filter(Boolean)) {
          current += '/' + part;
          try {
            FS.mkdir(current);
          } catch {
            // It exists.
          }
        }
        FS.mount(FS.filesystems.NODEFS, { root }, root);
        Module.ENV.LEAN_PATH = lib;
      },
    ];
    Module.onRuntimeInitialized = () => {
      try {
        Module._lean_initialize_runtime_module();
        Module._lean_initialize();
        Module._lean_io_mark_end_initialization();
        Module._lean_init_task_manager?.();
        Module._lean_enable_initializer_execution?.();
        const res = Module._lean_init_search_path();
        if ((Module.getValue(res + 7, 'i8') & 0xff) !== 0) throw new Error('lean_init_search_path failed');
        resolve();
      } catch (e) {
        reject(e as Error);
      }
    };
    Module.onAbort = (what: string) => reject(new Error(`Lean stopped: ${what}`));
  });
  (globalThis as { __leanModule?: unknown }).__leanModule = Module;
  const source = 'Module = globalThis.__leanModule;\n' + readFileSync(leanJs, 'utf8');
  const fn = vm.compileFunction(source, ['exports', 'require', 'module', '__filename', '__dirname'], {
    filename: leanJs,
  });
  fn({}, createRequire(leanJs), { exports: {} }, leanJs, bin);
  await ready;

  const str = (s: string) => {
    const p = Module.stringToNewUTF8(s);
    const o = Module._lean_mk_string(p);
    Module._free(p);
    return o;
  };
  capturing = true;
  const res = Module._lean_wasm_compile(str(code), str('Bundle.lean'));
  capturing = false;
  if ((Module.getValue(res + 7, 'i8') & 0xff) !== 0) throw new Error('Lean could not run the check');
  return diagnostics;
}

const examplesDir = path.join(site, '../examples');
const one = process.argv[2];
if (one != null) {
  // Child process: check one example and print its claims' statuses as JSON.
  const dir = path.join(examplesDir, one);
  const { src, theorems } = exampleFiles(dir);
  const files = [...src, ...theorems];
  const names = claims(files).map((c) => c.name);
  const b = bundle(readFileSync(goSpecPath, 'utf8'), leanInOrder(files), names);
  const result = statuses(await checkOne(b.text), b, names);
  process.stdout.write(JSON.stringify([...result]) + '\n');
  process.exit(0);
}

let failed = false;
for (const name of readdirSync(examplesDir).sort()) {
  const run = spawnSync(process.execPath, [import.meta.filename, name], { encoding: 'utf8' });
  const last = run.stdout.trim().split('\n').at(-1) ?? '';
  let result: [string, { kind: string; reason?: string }][] = [];
  try {
    result = JSON.parse(last) as typeof result;
  } catch {
    console.error(`${name}: Lean did not finish\n${run.stderr.slice(-2000)}`);
    failed = true;
    continue;
  }
  for (const [claim, status] of result) {
    const ok = status.kind === 'proved';
    if (!ok) failed = true;
    console.log(`${name}: ${claim} ${ok ? 'proved' : `${status.kind}: ${status.reason ?? ''}`}`);
  }
}
process.exit(failed ? 1 : 0);
