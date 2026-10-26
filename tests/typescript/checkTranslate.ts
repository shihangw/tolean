/**
 * Check the Lean translator (`tolean translate`) against the TypeScript one
 * in `npm/`, which reads the source with `tsc`.
 *
 *   cd tests/typescript && node checkTranslate.ts
 *
 * For each `corpus/translate/*.ts`, at each target in `TARGETS`:
 *
 * - if both accept it, the Lean files are the same, byte for byte, and Lean
 *   compiles them against this repository's runtime;
 * - if the TypeScript translator refuses it, the Lean one refuses it too.
 *
 * The Lean translator types the subset itself and may refuse more. It lists
 * those files; they are not failures.
 *
 * Run it in `nix develop`: it needs `lake`. The Lean translator is
 * `.lake/build/bin/tolean`, or `$TOLEAN`.
 */
import { spawnSync } from 'node:child_process';
import { mkdtempSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';

import { type Edition, TranslateError, translateSource } from '../../npm/src/translate.ts';

/** The corpus runs at each of these targets, so that both translators also
 * agree on which features each edition has. */
const TARGETS: ReadonlyArray<Edition> = ['ES2015', 'ES2019', 'ES2020', 'ES2024'];

const root = fileURLToPath(new URL('../../', import.meta.url));
const tolean = process.env.TOLEAN ?? join(root, '.lake/build/bin/tolean');
const out = mkdtempSync(join(tmpdir(), 'tolean-translate-'));

type Result = { kind: 'lean'; text: string } | { kind: 'refused'; message: string };

/** tsc refused only with lints that the translators do not model; the code
 * still has an exact meaning, so the Lean translator may accept it:
 *
 * - TS2367, "this comparison appears to be unintentional because the types
 *   have no overlap", as in `true === false`;
 * - TS2845, "this condition will always return 'false'", as in `x === NaN`;
 * - TS2322 into the type `true` or `false`: tsc gives `let b = c || true` the
 *   type `true`, so a later `b = x < y` fails. */
function onlyLints(message: string): boolean {
  const errors = [...message.matchAll(/error TS(\d+): ([^\n]*)/g)];
  return (
    errors.length > 0 &&
    errors.every(
      ([, code, text]) =>
        code === '2367' ||
        code === '2845' ||
        (code === '2322' && /to type '(true|false)'/.test(text ?? '')),
    )
  );
}

function short(message: string): string {
  return message.split('\n').filter((l) => l.trim() !== '').slice(0, 3).join(' | ');
}

function typescript(path: string, target?: Edition): Result {
  try {
    return {
      kind: 'lean',
      text: translateSource({
        fileName: path,
        text: readFileSync(path, 'utf8'),
        namespace: 'Test',
        ...(target === undefined ? {} : { target }),
      }),
    };
  } catch (error) {
    if (error instanceof TranslateError) {
      return { kind: 'refused', message: error.message };
    }
    throw error;
  }
}

function lean(path: string, output: string, target?: Edition): Result {
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

function firstDifference(lean: string, ts: string): string {
  const a = lean.split('\n');
  const b = ts.split('\n');
  for (let i = 0; i < Math.max(a.length, b.length); i++) {
    if (a[i] !== b[i]) {
      return `line ${i + 1}:\n  lean: ${a[i] ?? '(none)'}\n  ts:   ${b[i] ?? '(none)'}`;
    }
  }
  return '(none)';
}

const failures: Array<string> = [];
const stricter: Array<string> = [];
let equal = 0;
let bothRefuse = 0;
let lint = 0;

const files = readdirSync('corpus/translate')
  .filter((f) => f.endsWith('.ts'))
  .sort();
for (const target of TARGETS) for (const file of files) {
  const path = `corpus/translate/${file}`;
  const output = join(out, `${target}-${file.replace(/\.ts$/, '.lean')}`);
  const expected = typescript(path, target);
  const actual = lean(path, output, target);
  if (expected.kind === 'lean' && actual.kind === 'lean') {
    if (actual.text !== expected.text) {
      failures.push(`${path} (${target}): the outputs differ\n--- typescript\n${expected.text}\n--- lean\n${actual.text}`);
      continue;
    }
    const error = compiles(output);
    if (error !== null) {
      failures.push(`${path} (${target}): the Lean output does not compile:\n${error}`);
      continue;
    }
    equal++;
  } else if (expected.kind === 'refused' && actual.kind === 'refused') {
    bothRefuse++;
  } else if (actual.kind === 'refused') {
    stricter.push(`${path} (${target}): ${actual.message}`);
  } else if (expected.kind === 'refused' && onlyLints(expected.message)) {
    lint++;
  } else {
    failures.push(`${path} (${target}): only the TypeScript translator refuses it: ${expected.kind === 'refused' ? short(expected.message) : ''}`);
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
const tally = { equal: 0, bothRefuse: 0, stricter: 0 };
const stricterReasons = new Map<string, number>();
for (let i = 0; i < fuzzCount; i++) {
  const caseSeed = seed + i;
  const path = join(fuzzDir, `case${caseSeed}.ts`);
  writeFileSync(path, new Gen(caseSeed).program());
  const output = join(fuzzDir, `case${caseSeed}.lean`);
  const expected = typescript(path);
  const actual = lean(path, output);
  if (expected.kind === 'lean' && actual.kind === 'lean') {
    if (actual.text !== expected.text) {
      failures.push(`fuzz seed ${caseSeed} (${path}): the outputs differ at ${firstDifference(actual.text, expected.text)}`);
    } else {
      const error = compiles(output);
      if (error === null) {
        tally.equal++;
      } else {
        failures.push(`fuzz seed ${caseSeed} (${path}): the Lean output does not compile:\n${error.slice(0, 600)}`);
      }
    }
  } else if (expected.kind === 'refused' && actual.kind === 'refused') {
    tally.bothRefuse++;
  } else if (actual.kind === 'refused') {
    tally.stricter++;
    const reason = actual.message.replace(/^[^:]*:\d+:\d+: /, '').replace(/: .*$/, '');
    stricterReasons.set(reason, (stricterReasons.get(reason) ?? 0) + 1);
  } else if (expected.kind === 'refused' && onlyLints(expected.message)) {
    lint++;
  } else {
    failures.push(`fuzz seed ${caseSeed} (${path}): only the TypeScript translator refuses it: ${expected.kind === 'refused' ? short(expected.message) : ''}`);
  }
}
console.log(
  `fuzz: ${fuzzCount} programs from seed ${seed}: ${tally.equal} equal and compiled, ` +
    `${tally.bothRefuse} refused by both, ${tally.stricter} refused only by the Lean translator, ` +
    `${lint} accepted by Lean where tsc reports only lints`,
);
for (const [reason, n] of [...stricterReasons].sort((x, y) => y[1] - x[1])) {
  console.log(`  stricter: ${n}× ${reason}`);
}

console.log(
  `translate: ${files.length} files at ${TARGETS.join(', ')}: ${equal} equal and compiled, ${bothRefuse} refused by both, ` +
    `${stricter.length} refused only by the Lean translator`,
);
for (const s of stricter) {
  console.log(`  stricter: ${s}`);
}
for (const f of failures) {
  console.error(`FAIL ${f}`);
}
process.exit(failures.length === 0 ? 0 : 1);
