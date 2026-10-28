/**
 * Check the Lean TypeScript translator (`tolean translate`) on the corpus and
 * on random programs.
 *
 *   cd tests/typescript && node checkTranslate.ts [--fuzz <count>] [--seed <n>] [--update] [--require-wasm]
 *
 * - `corpus/translate/accept/*.ts`: the translation equals the committed
 *   `.lean` file beside it, and Lean compiles it. `--update` rewrites those
 *   files instead, for a change to the output that is meant.
 * - `corpus/translate/reject/*.ts`: the translator refuses the file. A line
 *   `// expect: <line>:<col> <part of the message>` says where and why.
 * - In both, a line `// target: ES20xx` translates for that edition instead of
 *   the default.
 * - `corpus/translate/projects/accept/<name>/`: a project of several files,
 *   with a `tolean.json`. `tolean translate --check` finds its committed Lean
 *   current, and Lean compiles each module after the modules it imports.
 *   `--update` runs `tolean translate` there instead.
 * - `corpus/translate/projects/reject/<name>/`: `tolean translate` refuses the
 *   project, with a message that contains the text of its `expect.txt`.
 * - Fuzz: random programs (default 200). When the translator accepts one, the
 *   output compiles, and a second translation gives the same text.
 * - Everywhere, when `wasm/out` exists (from `wasm/build.sh`): the
 *   playground's WebAssembly build gives the same result as the native
 *   command, the same Lean or the same refusal. The two are compiled from the
 *   same Lean, but for different machines, so this catches a miscompilation
 *   on either one. `--require-wasm` fails when `wasm/out` does not exist.
 *
 * Nothing here is a second translator, so a golden file shows only that the
 * output did not change and still compiles; a person read it once. Per-file
 * certificates (`checkCertify.sh`) prove the translation for the files they
 * cover.
 *
 * Run it in `nix develop`: it needs `lake`. The translator is
 * `.lake/build/bin/tolean`, or `$TOLEAN`.
 */
import { spawnSync } from 'node:child_process';
import { cpSync, existsSync, mkdirSync, mkdtempSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';

import { Gen } from './gen.ts';


const root = fileURLToPath(new URL('../../', import.meta.url));
const tolean = process.env.TOLEAN ?? join(root, '.lake/build/bin/tolean');
const out = mkdtempSync(join(tmpdir(), 'tolean-translate-'));
const update = process.argv.includes('--update');
const wasmOut = fileURLToPath(new URL('../../wasm/out/tolean.js', import.meta.url));
if (process.argv.includes('--require-wasm') && !existsSync(wasmOut)) {
  console.error('wasm/out has no translator; run wasm/build.sh');
  process.exit(1);
}
// Loaded only when it exists, because loading it starts the translator.
const translateInWasm = existsSync(wasmOut) ? (await import('./wasm.ts')).translateInWasm : null;

type Result = { kind: 'lean'; text: string } | { kind: 'refused'; message: string };

function lean(path: string, output: string, target?: string): Result {
  const args = target === undefined ? [] : ['--target', target];
  const run = spawnSync(tolean, ['translate', ...args, path, output, 'Test'], { encoding: 'utf8' });
  if (run.error !== undefined) {
    throw run.error;
  }
  if (run.status === 0) {
    return { kind: 'lean', text: readFileSync(output, 'utf8') };
  }
  if (run.status === 1) {
    return { kind: 'refused', message: run.stderr.trim() };
  }
  throw new Error(`tolean translate ${path} exited with ${run.status}: ${run.stderr}`);
}

function compiles(output: string): string | null {
  const run = spawnSync('lake', ['env', 'lean', output], { cwd: root, encoding: 'utf8' });
  if (run.error !== undefined) {
    throw run.error;
  }
  if (run.status === 0) {
    return null;
  }
  // Only the errors: the unused-variable warnings are noise here.
  return (run.stdout + run.stderr)
    .split('\n')
    .filter((line) => line.includes(': error') || line.startsWith('  '))
    .join('\n')
    .trim();
}

let agreed = 0;

/** Fail unless the WebAssembly build gives the native result. */
async function sameInWasm(path: string, native: Result, target?: string): Promise<void> {
  if (translateInWasm === null) return;
  const other = translateInWasm(path, readFileSync(path, 'utf8'), target);
  const same =
    native.kind === other.kind &&
    (native.kind === 'lean' ? native.text === (other as typeof native).text : native.message === (other as { message: string }).message);
  if (same) agreed++;
  else failures.push(`${path}: the WebAssembly build differs from the native command:\n  native: ${JSON.stringify(native).slice(0, 300)}\n  wasm:   ${JSON.stringify(other).slice(0, 300)}`);
}

/** The value of a `// <key>: <value>` line in a corpus file. */
function directive(text: string, key: string): string | undefined {
  return new RegExp(`^// ${key}: (.*)$`, 'm').exec(text)?.[1]?.trim();
}

const failures: Array<string> = [];

const accept = readdirSync('corpus/translate/accept').filter((f) => f.endsWith('.ts')).sort();
for (const file of accept) {
  const path = `corpus/translate/accept/${file}`;
  const golden = path.replace(/\.ts$/, '.lean');
  const output = join(out, file.replace(/\.ts$/, '.lean'));
  const target = directive(readFileSync(path, 'utf8'), 'target');
  const result = lean(path, output, target);
  await sameInWasm(path, result, target);
  if (result.kind === 'refused') {
    failures.push(`${path}: refused: ${result.message}`);
    continue;
  }
  if (update) {
    writeFileSync(golden, result.text);
  } else if (result.text !== readFileSync(golden, 'utf8')) {
    failures.push(`${path}: the output differs from ${golden}; run with --update if the change is meant`);
    continue;
  }
  const error = compiles(output);
  if (error !== null) {
    failures.push(`${path}: the Lean output does not compile:\n${error}`);
  }
}

const reject = readdirSync('corpus/translate/reject').filter((f) => f.endsWith('.ts')).sort();
for (const file of reject) {
  const path = `corpus/translate/reject/${file}`;
  const text = readFileSync(path, 'utf8');
  const expect = directive(text, 'expect');
  const where = expect === undefined ? null : /^(\d+):(\d+) (.*)$/.exec(expect);
  if (where == null) {
    failures.push(`${path}: the first lines need '// expect: <line>:<col> <part of the message>'`);
    continue;
  }
  const result = lean(path, join(out, file.replace(/\.ts$/, '.lean')), directive(text, 'target'));
  await sameInWasm(path, result, directive(text, 'target'));
  if (result.kind === 'lean') {
    failures.push(`${path}: accepted, but it should be refused`);
  } else if (!result.message.startsWith(`${path}:${where[1]}:${where[2]}: `) || !result.message.includes(where[3]!)) {
    failures.push(`${path}: refused with '${result.message}', expected ${where[1]}:${where[2]} '${where[3]}'`);
  }
}

// ---------------------------------------------------------------------------
// Projects of several files.

/** The `.lean` files under `dir`, as paths relative to it. */
function leanFiles(dir: string, prefix = ''): Array<string> {
  return readdirSync(join(dir, prefix), { withFileTypes: true }).flatMap((e) => {
    const rel = prefix === '' ? e.name : `${prefix}/${e.name}`;
    if (e.isDirectory()) return leanFiles(dir, rel);
    return e.name.endsWith('.lean') ? [rel] : [];
  });
}

/** The Lean search path of the root package, for compiling a project's modules. */
function rootLeanPath(): string {
  const run = spawnSync('lake', ['env', 'printenv', 'LEAN_PATH'], { cwd: root, encoding: 'utf8' });
  if (run.error !== undefined) throw run.error;
  if (run.status !== 0) throw new Error(`lake env printenv LEAN_PATH exited with ${run.status}: ${run.stderr}`);
  return run.stdout.trim();
}

/** Compile the Lean modules of `dir`, each after the modules of `dir` that it
imports, and give the first error, or null. */
function compilesProject(dir: string, leanPath: string): string | null {
  const copy = mkdtempSync(join(tmpdir(), 'tolean-project-'));
  cpSync(dir, copy, { recursive: true });
  // Module names start at `moduleRoot`, as they do in the project's Lean package.
  const config = JSON.parse(readFileSync(join(dir, 'tolean.json'), 'utf8'));
  const build = join(copy, config.typescript?.moduleRoot ?? '');
  const modules = new Map(leanFiles(build).map((f) => [f.replace(/\.lean$/, '').replaceAll('/', '.'), f]));
  const done = new Set<string>();
  const visit = (name: string): string | null => {
    if (done.has(name)) return null;
    done.add(name);
    const file = modules.get(name)!;
    const text = readFileSync(join(build, file), 'utf8');
    for (const [, written] of text.matchAll(/^import (\S+)$/gm)) {
      const dep = written!.replaceAll(/[«»]/g, '');
      if (modules.has(dep)) {
        const error = visit(dep);
        if (error !== null) return error;
      }
    }
    const olean = join(build, file.replace(/\.lean$/, '.olean'));
    mkdirSync(join(olean, '..'), { recursive: true });
    const run = spawnSync('lean', ['--root=.', '-o', olean, file], {
      cwd: build,
      encoding: 'utf8',
      env: { ...process.env, LEAN_PATH: `${build}:${leanPath}` },
    });
    if (run.error !== undefined) throw run.error;
    return run.status === 0 ? null : `${file}: ${(run.stdout + run.stderr).trim().slice(0, 600)}`;
  };
  for (const name of modules.keys()) {
    const error = visit(name);
    if (error !== null) return error;
  }
  return null;
}

const projectsDir = 'corpus/translate/projects';
const acceptProjects = readdirSync(`${projectsDir}/accept`).sort();
const leanPath = rootLeanPath();
for (const name of acceptProjects) {
  const dir = `${projectsDir}/accept/${name}`;
  const run = spawnSync(tolean, update ? ['translate'] : ['translate', '--check'], { cwd: dir, encoding: 'utf8' });
  if (run.status !== 0) {
    failures.push(`${dir}: tolean translate${update ? '' : ' --check'} failed: ${run.stderr.trim()}`);
    continue;
  }
  const error = compilesProject(dir, leanPath);
  if (error !== null) failures.push(`${dir}: the Lean output does not compile:\n${error}`);
}
const rejectProjects = readdirSync(`${projectsDir}/reject`).sort();
for (const name of rejectProjects) {
  const dir = `${projectsDir}/reject/${name}`;
  const expect = readFileSync(join(dir, 'expect.txt'), 'utf8').trim();
  const build = mkdtempSync(join(tmpdir(), 'tolean-project-'));
  cpSync(dir, build, { recursive: true });
  const run = spawnSync(tolean, ['translate'], { cwd: build, encoding: 'utf8' });
  if (run.status === 0) failures.push(`${dir}: accepted, but it should be refused`);
  else if (!run.stderr.includes(expect)) failures.push(`${dir}: refused with '${run.stderr.trim()}', expected '${expect}'`);
}

// ---------------------------------------------------------------------------
// Random programs in the subset, built by type, so that most are valid.

function flag(name: string): number | undefined {
  const i = process.argv.indexOf(name);
  const value = i < 0 ? undefined : process.argv[i + 1];
  return value === undefined ? undefined : Number(value);
}

const fuzzCount = flag('--fuzz') ?? 200;
const seed = flag('--seed') ?? Math.floor(Math.random() * 1e9);
const fuzzDir = mkdtempSync(join(tmpdir(), 'tolean-translate-fuzz-'));
const tally = { compiled: 0, refused: 0 };
const reasons = new Map<string, number>();
for (let i = 0; i < fuzzCount; i++) {
  const caseSeed = seed + i;
  const path = join(fuzzDir, `case${caseSeed}.ts`);
  writeFileSync(path, new Gen(caseSeed).program());
  const output = join(fuzzDir, `case${caseSeed}.lean`);
  const first = lean(path, output);
  await sameInWasm(path, first);
  if (first.kind === 'refused') {
    tally.refused++;
    const reason = first.message.replace(/^[^:]*:\d+:\d+: /, '').replace(/: .*$/, '');
    reasons.set(reason, (reasons.get(reason) ?? 0) + 1);
    continue;
  }
  const second = lean(path, join(fuzzDir, `case${caseSeed}.again.lean`));
  if (second.kind !== 'lean' || second.text !== first.text) {
    failures.push(`fuzz seed ${caseSeed} (${path}): a second translation gives another result`);
    continue;
  }
  const error = compiles(output);
  if (error === null) {
    tally.compiled++;
  } else {
    failures.push(`fuzz seed ${caseSeed} (${path}): the Lean output does not compile:\n${error.slice(0, 600)}`);
  }
}
console.log(`fuzz: ${fuzzCount} programs from seed ${seed}: ${tally.compiled} translated and compiled, ${tally.refused} refused`);
for (const [reason, n] of [...reasons].sort((x, y) => y[1] - x[1])) {
  console.log(`  refused: ${n}× ${reason}`);
}

console.log(
  `translate: ${accept.length} accepted files${update ? ' (golden files rewritten)' : ''}, ${reject.length} refused files`,
);
console.log(`projects: ${acceptProjects.length} accepted, ${rejectProjects.length} refused`);
console.log(
  translateInWasm === null
    ? 'wasm: skipped, because wasm/out has no translator'
    : `wasm: ${agreed} files and programs where the WebAssembly build gives the native result`,
);
for (const f of failures) {
  console.error(`FAIL ${f}`);
}
process.exit(failures.length === 0 ? 0 : 1);
