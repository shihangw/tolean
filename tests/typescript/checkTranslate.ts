/**
 * Check the Lean TypeScript translator (`tolean translate`) on the corpus and
 * on random programs.
 *
 *   cd tests/typescript && node checkTranslate.ts [--fuzz <count>] [--seed <n>] [--update]
 *
 * - `corpus/translate/accept/*.ts`: the translation equals the committed
 *   `.lean` file beside it, and Lean compiles it. `--update` rewrites those
 *   files instead, for a change to the output that is meant.
 * - `corpus/translate/reject/*.ts`: the translator refuses the file. A line
 *   `// expect: <line>:<col> <part of the message>` says where and why.
 * - In both, a line `// target: ES20xx` translates for that edition instead of
 *   the default.
 * - Fuzz: random programs (default 200). When the translator accepts one, the
 *   output compiles, and a second translation gives the same text.
 * - Everywhere: the playground's WebAssembly build (`wasm/out`, from
 *   `wasm/build.sh`) gives the same result as the native
 *   command, the same Lean or the same refusal. The two are compiled from the
 *   same Lean, but for different machines, so this catches a miscompilation
 *   on either one.
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
import { mkdtempSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';

import { translateInWasm } from './wasm.ts';

const root = fileURLToPath(new URL('../../', import.meta.url));
const tolean = process.env.TOLEAN ?? join(root, '.lake/build/bin/tolean');
const out = mkdtempSync(join(tmpdir(), 'tolean-translate-'));
const update = process.argv.includes('--update');

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
// Random programs in the subset, built by type, so that most are valid.

function random(seed: number): () => number {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

type Ty =
  | { k: 'bigint' }
  | { k: 'number' }
  | { k: 'boolean' }
  | { k: 'nullable'; of: Ty }
  | { k: 'array'; of: Ty }
  | { k: 'struct'; name: string };

type Var = { name: string; ty: Ty; mutable: boolean; owned: boolean };

const BIGINT: Ty = { k: 'bigint' };
const NUMBER: Ty = { k: 'number' };
const BOOLEAN: Ty = { k: 'boolean' };

function same(a: Ty, b: Ty): boolean {
  return JSON.stringify(a) === JSON.stringify(b);
}

function show(t: Ty): string {
  switch (t.k) {
    case 'bigint':
    case 'number':
    case 'boolean':
      return t.k;
    case 'nullable':
      return `${show(t.of)} | null`;
    case 'array':
      return `ReadonlyArray<${show(t.of)}>`;
    case 'struct':
      return t.name;
  }
}

class Gen {
  private readonly next: () => number;
  private structs: Array<{ name: string; fields: Array<[string, Ty]> }> = [];
  private functions: Array<{ name: string; params: Array<Ty>; ret: Ty }> = [];
  private counter = 0;

  constructor(seed: number) {
    this.next = random(seed);
  }

  private chance(p: number): boolean {
    return this.next() < p;
  }

  private pick<T>(xs: ReadonlyArray<T>): T {
    const x = xs[Math.floor(this.next() * xs.length)];
    if (x === undefined) {
      throw new Error('empty choice');
    }
    return x;
  }

  private fresh(prefix: string): string {
    this.counter++;
    return `${prefix}${this.counter}`;
  }

  private scalar(): Ty {
    return this.pick([BIGINT, BIGINT, NUMBER, NUMBER, BOOLEAN]);
  }

  private anyType(): Ty {
    const roll = this.next();
    if (roll < 0.5) {
      return this.scalar();
    }
    if (roll < 0.65) {
      return { k: 'nullable', of: this.pick([BIGINT, NUMBER]) };
    }
    if (roll < 0.8 && this.structs.length > 0) {
      return { k: 'struct', name: this.pick(this.structs).name };
    }
    return { k: 'array', of: this.pick([BIGINT, NUMBER, ...this.structs.map((s): Ty => ({ k: 'struct', name: s.name }))]) };
  }

  /** An expression of type `t`, reading only `vars`. */
  expr(t: Ty, vars: ReadonlyArray<Var>, depth: number): string {
    const readable = vars.filter((v) => !v.owned);
    const ofType = readable.filter((v) => same(v.ty, t));
    const leaf = (): string => {
      if (ofType.length > 0 && this.chance(0.6)) {
        return this.pick(ofType).name;
      }
      switch (t.k) {
        case 'bigint':
          return this.pick(['0n', '1n', '7n', '0x1fn', '1_000n']);
        case 'number':
          return this.pick(['0', '1', '42', '1e3', '0x10', 'NaN', 'Infinity', '-Infinity']);
        case 'boolean':
          return this.pick(['true', 'false']);
        case 'nullable':
          return this.chance(0.5) ? 'null' : this.expr(t.of, vars, 0);
        case 'struct':
          return this.object(t.name, vars, 0);
        case 'array': {
          const any = readable.filter((v) => v.ty.k === 'array' && same(v.ty, t));
          return any.length > 0 ? this.pick(any).name : 'null as never';
        }
      }
    };
    if (depth <= 0 || this.chance(0.3)) {
      return leaf();
    }
    const d = depth - 1;
    const fields = this.fieldReads(t, readable);
    const calls = this.functions.filter((f) => same(f.ret, t));
    const options: Array<() => string> = [leaf];
    if (fields.length > 0) {
      options.push(() => this.pick(fields));
    }
    if (calls.length > 0) {
      options.push(() => {
        const f = this.pick(calls);
        return `${f.name}(${f.params.map((p) => this.expr(p, vars, d)).join(', ')})`;
      });
    }
    options.push(() => `(${this.test(vars, d)} ? ${this.expr(t, vars, d)} : ${this.expr(t, vars, d)})`);
    switch (t.k) {
      case 'bigint':
      case 'number':
        options.push(
          () => `${this.expr(t, vars, d)} ${this.pick(['+', '-', '*'])} ${this.expr(t, vars, d)}`,
          () => `-${this.expr(t, vars, d)}`,
          () => `(${this.expr(t, vars, d)})`,
        );
        if (t.k === 'bigint') {
          // Both translators accept a nonzero literal divisor only.
          options.push(() => `${this.expr(t, vars, d)} ${this.pick(['/', '%'])} ${this.pick(['2n', '-3n', '(7n)', '-(5n)', '0n', this.expr(t, vars, 0)])}`);
        }
        break;
      case 'boolean': {
        const nullable = readable.filter((v) => v.ty.k === 'nullable');
        options.push(
          () => {
            const u = this.pick([BIGINT, NUMBER]);
            return `${this.expr(u, vars, d)} ${this.pick(['<', '<=', '>', '>=', '===', '!=='])} ${this.expr(u, vars, d)}`;
          },
          () => `${this.expr(BOOLEAN, vars, d)} ${this.pick(['&&', '||'])} ${this.expr(BOOLEAN, vars, d)}`,
          () => `!${this.expr(BOOLEAN, vars, d)}`,
          // Not two literals: tsc refuses \`true === false\` (TS2367), and narrows
          // oddly in the branch \`true === true\` makes impossible.
          () => {
            const flags = readable.filter((v) => v.ty.k === 'boolean');
            return flags.length > 0 ? `${this.pick(flags).name} === ${this.expr(BOOLEAN, vars, d)}` : 'true';
          },
          () => `Number.${this.pick(['isNaN', 'isFinite', 'isSafeInteger'])}(${this.expr(NUMBER, vars, d)})`,
        );
        if (nullable.length > 0) {
          options.push(() => {
            const v = this.pick(nullable);
            const narrowed = vars.map((x) => (x.name === v.name && x.ty.k === 'nullable' ? { ...x, ty: x.ty.of } : x));
            return this.chance(0.5)
              ? `${v.name} === null || ${this.expr(BOOLEAN, narrowed, d)}`
              : `${v.name} !== null && ${this.expr(BOOLEAN, narrowed, d)}`;
          }, () => `${this.pick(nullable).name} ${this.pick(['===', '!=='])} null`);
        }
        break;
      }
      default:
        break;
    }
    return this.pick(options)();
  }

  /** A condition that is not a literal. With a literal test, such as
   * `true ? a : b`, tsc drops its null narrowing in the impossible branch and
   * reports an error there; that is a quirk of tsc on dead code, not a type
   * error the translators need to agree on. */
  private test(vars: ReadonlyArray<Var>, depth: number): string {
    const flags = vars.filter((v) => !v.owned && v.ty.k === 'boolean');
    if (flags.length > 0 && this.chance(0.5)) {
      return this.pick(flags).name;
    }
    const u = this.pick([BIGINT, NUMBER]);
    const numeric = vars.filter((v) => !v.owned && same(v.ty, u));
    const left = numeric.length > 0 ? this.pick(numeric).name : this.expr(u, vars, depth);
    return `${left} ${this.pick(['<', '<=', '>', '>='])} ${this.expr(u, vars, depth)}`;
  }

  private fieldReads(t: Ty, vars: ReadonlyArray<Var>): Array<string> {
    const reads: Array<string> = [];
    for (const v of vars) {
      if (v.ty.k !== 'struct') {
        continue;
      }
      const name = v.ty.name;
      const s = this.structs.find((x) => x.name === name);
      for (const [field, ty] of s?.fields ?? []) {
        if (same(ty, t)) {
          reads.push(`${v.name}.${field}`);
        }
      }
    }
    return reads;
  }

  private object(name: string, vars: ReadonlyArray<Var>, depth: number): string {
    const s = this.structs.find((x) => x.name === name);
    const parts = (s?.fields ?? []).map(([field, ty]) => {
      const v = vars.find((x) => x.name === field && same(x.ty, ty) && !x.owned);
      return v !== undefined && this.chance(0.5) ? field : `${field}: ${this.expr(ty, vars, depth)}`;
    });
    return `{ ${parts.join(', ')} }`;
  }

  private body(vars: Array<Var>, ret: Ty, depth: number, inLoop: boolean): Array<string> {
    const lines: Array<string> = [];
    const count = 1 + Math.floor(this.next() * 3);
    for (let i = 0; i < count; i++) {
      const roll = this.next();
      const lets = vars.filter((v) => v.mutable);
      if (roll < 0.3) {
        const t = this.pick([BIGINT, NUMBER, BOOLEAN, ...(this.structs.length > 0 ? [{ k: 'struct', name: this.pick(this.structs).name } as Ty] : [])]);
        const name = this.fresh('v');
        const mutable = this.chance(0.6);
        const annotate = t.k === 'struct' || this.chance(0.2);
        lines.push(`${mutable ? 'let' : 'const'} ${name}${annotate ? `: ${show(t)}` : ''} = ${this.expr(t, vars, 2)};`);
        vars.push({ name, ty: t, mutable, owned: false });
      } else if (roll < 0.5 && lets.length > 0) {
        const v = this.pick(lets);
        const op = v.ty.k === 'bigint' || v.ty.k === 'number' ? this.pick(['=', '+=', '-=', '*=']) : '=';
        lines.push(`${v.name} ${op} ${this.expr(v.ty, vars, 2)};`);
      } else if (roll < 0.65 && depth > 0 && lets.length > 0) {
        const v = this.pick(lets);
        lines.push(`if (${this.test(vars, 2)}) {`, `  ${v.name} = ${this.expr(v.ty, vars, 1)};`, '}');
      } else if (roll < 0.8 && depth > 0) {
        const arrays = vars.filter((v) => v.ty.k === 'array' && !v.owned);
        const target = lets.length > 0 ? this.pick(lets) : undefined;
        if (arrays.length > 0 && target !== undefined) {
          const xs = this.pick(arrays);
          if (xs.ty.k === 'array') {
            const element = this.fresh('e');
            const inner = [...vars, { name: element, ty: xs.ty.of, mutable: false, owned: false }];
            lines.push(`for (const ${element} of ${xs.name}) {`, `  ${target.name} = ${this.expr(target.ty, inner, 1)};`, '}');
          }
        }
      } else if (!inLoop && this.chance(0.3)) {
        // Rarely, something outside the subset or ill-typed, to check that both refuse.
        lines.push(this.pick([
          `const bad${this.counter} = 5n / 2n;`,
          `let w${this.counter} = 1; w${this.counter} = true;`,
          `const q${this.counter} = ${vars[0]?.name ?? 'x'}.missing;`,
        ]));
      }
    }
    lines.push(`return ${this.expr(ret, vars, 2)};`);
    return lines;
  }

  program(): string {
    const out: Array<string> = [];
    const structCount = Math.floor(this.next() * 3);
    for (let i = 0; i < structCount; i++) {
      const name = `S${i}`;
      const fields: Array<[string, Ty]> = [];
      const n = 1 + Math.floor(this.next() * 3);
      for (let j = 0; j < n; j++) {
        fields.push([`f${j}`, this.pick([BIGINT, NUMBER, BOOLEAN, { k: 'nullable', of: NUMBER } as Ty])]);
      }
      out.push(`interface ${name} {`, ...fields.map(([f, t]) => `  readonly ${f}: ${show(t)};`), '}');
      this.structs.push({ name, fields });
    }
    const fnCount = 1 + Math.floor(this.next() * 3);
    for (let i = 0; i < fnCount; i++) {
      const name = `fn${i}`;
      const params: Array<Ty> = [];
      const vars: Array<Var> = [];
      const pc = Math.floor(this.next() * 4);
      for (let j = 0; j < pc; j++) {
        const t = this.anyType();
        params.push(t);
        vars.push({ name: `p${j}`, ty: t, mutable: false, owned: false });
      }
      const ret = this.chance(0.3) && this.structs.length > 0 ? ({ k: 'struct', name: this.pick(this.structs).name } as Ty) : this.scalar();
      const signature = vars.map((v) => `${v.name}: ${show(v.ty)}`).join(', ');
      const nullable = vars.filter((v) => v.ty.k === 'nullable');
      const lines: Array<string> = [];
      if (nullable.length > 0 && this.chance(0.5)) {
        // `if (x === null) return …;` narrows `x` in the rest of the body.
        const v = this.pick(nullable);
        lines.push(`if (${v.name} === null) {`, `  return ${this.expr(ret, vars, 1)};`, '}');
        if (v.ty.k === 'nullable') {
          v.ty = v.ty.of;
        }
      }
      lines.push(...this.body(vars, ret, 2, false));
      out.push(`export function ${name}(${signature}): ${show(ret)} {`, ...lines.map((l) => `  ${l}`), '}');
      this.functions.push({ name, params, ret });
    }
    return out.join('\n') + '\n';
  }
}

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
console.log(`wasm: ${agreed} files and programs where the WebAssembly build gives the native result`);
for (const f of failures) {
  console.error(`FAIL ${f}`);
}
process.exit(failures.length === 0 ? 0 : 1);
