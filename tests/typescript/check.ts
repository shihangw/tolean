/**
 * Check the Lean TypeScript parser against `tsc`.
 *
 *   node tests/typescript/check.ts [--fuzz <count>] [--seed <n>]
 *
 * - `corpus/parse/accept/*.ts`: both parsers accept the file, and the trees
 *   are equal.
 * - `corpus/parse/reject/*.ts`: the Lean parser refuses the file. Its first
 *   line is `// expect: <line>:<col> <part of the message>`. A line
 *   `// target: ES20xx` parses it for that edition instead of the default.
 * - Fuzz: random programs (default 500). For each, the trees are equal, or
 *   both parsers refuse it, or the Lean parser refuses code that `tsc` could read
 *   another way (type arguments, an arrow function): it is stricter there on
 *   purpose.
 *
 * The Lean parser is `.lake/build/bin/tolean`, or `$TOLEAN`.
 */
import { spawnSync } from 'node:child_process';
import { mkdtempSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';

import { tscAst } from './tscAst.ts';

const here = fileURLToPath(new URL('.', import.meta.url));
const tolean = process.env.TOLEAN ?? fileURLToPath(new URL('../../.lake/build/bin/tolean', import.meta.url));
const CONSERVATIVE = 'tsc may read this';

type LeanResult = { kind: 'tree'; sexp: string } | { kind: 'refused'; message: string };

function lean(path: string, target?: string): LeanResult {
  const args = target === undefined ? [] : ['--target', target];
  const run = spawnSync(tolean, ['parse', ...args, path], { encoding: 'utf8' });
  if (run.error !== undefined) {
    throw run.error;
  }
  if (run.status === 0) {
    return { kind: 'tree', sexp: run.stdout.trimEnd() };
  }
  if (run.status === 1) {
    return { kind: 'refused', message: run.stderr.trim() };
  }
  throw new Error(`tolean parse ${path} exited with ${run.status}: ${run.stderr}`);
}

function firstDifference(a: string, b: string): string {
  const left = a.split('\n');
  const right = b.split('\n');
  for (let i = 0; i < Math.max(left.length, right.length); i++) {
    if (left[i] !== right[i]) {
      return `line ${i + 1}:\n  lean: ${left[i] ?? '(none)'}\n  tsc:  ${right[i] ?? '(none)'}`;
    }
  }
  return '(no difference)';
}

const failures: Array<string> = [];

function checkAccept(path: string): void {
  const text = readFileSync(path, 'utf8');
  const expected = tscAst(path, text);
  const actual = lean(path);
  if (expected.kind === 'refused') {
    failures.push(`${path}: the reference refuses it: ${expected.reason}`);
  } else if (actual.kind === 'refused') {
    failures.push(`${path}: the Lean parser refuses it: ${actual.message}`);
  } else if (actual.sexp !== expected.sexp) {
    failures.push(`${path}: the trees differ at ${firstDifference(actual.sexp, expected.sexp)}`);
  }
}

function checkReject(path: string): void {
  const text = readFileSync(path, 'utf8');
  const match = /^\/\/ expect: (\d+:\d+) (.+)$/m.exec(text.split('\n')[0] ?? '');
  if (match === null) {
    failures.push(`${path}: the first line must be '// expect: <line>:<col> <message part>'`);
    return;
  }
  const [, at, part] = match;
  const target = /^\/\/ target: (\S+)$/m.exec(text)?.[1];
  const actual = lean(path, target);
  if (actual.kind === 'tree') {
    failures.push(`${path}: the Lean parser accepts it`);
  } else if (!actual.message.includes(`:${at}: `) || !actual.message.includes(part ?? '')) {
    failures.push(`${path}: expected '${at} ${part}', got '${actual.message}'`);
  }
}

function corpus(dir: string): Array<string> {
  return readdirSync(join(here, dir))
    .filter((f) => f.endsWith('.ts'))
    .sort()
    .map((f) => join(here, dir, f));
}

// ---------------------------------------------------------------------------
// Random programs.

/** mulberry32: a small seeded generator, so a failure can be replayed. */
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

class Gen {
  private readonly next: () => number;

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

  /** Tokens joined by random white space, line breaks and comments. */
  join(tokens: ReadonlyArray<string>): string {
    return tokens
      .map((t, i) =>
        i === 0 ? t : this.separator() + t,
      )
      .join('');
  }

  /** Mostly a space; sometimes a line break or a comment, which change automatic
   * semicolon insertion and the spans. */
  private separator(): string {
    if (this.chance(0.8)) {
      return ' ';
    }
    return this.pick(['\n', '\t', ' /* c */ ', '/*\n*/', ' // c\n', '\r\n', '\u2028']);
  }

  private name(): string {
    return this.pick(['a', 'b', 'x', 'n', 'item', 'of', 'type', 'async', 'get', 'undefined', '$v', '_w']);
  }

  private atom(): Array<string> {
    return [
      this.pick([
        this.name(),
        this.name(),
        this.pick(['0', '1', '42', '1.5', '.5', '1e3', '2E-2', '0x1F', '0b101', '0o17', '1_000', '1.']),
        this.pick(['0n', '10n', '0xffn']),
        this.pick(["'a'", '"b\\n"', "'é'", "'\\u{1F600}'", '"\\x41\\u0042"', "' '", "'😀'", "'it\\'s'"]),
        this.pick(['true', 'false', 'null']),
      ]),
    ];
  }

  private target(depth: number): Array<string> {
    return this.pick([
      () => [this.name()],
      () => [this.name(), '.', this.pick(['p', 'default', 'if', 'new'])],
      () => [this.name(), '[', ...this.expr(depth - 1), ']'],
      () => ['(', this.name(), ')'],
    ])();
  }

  expr(depth: number): Array<string> {
    if (depth <= 0 || this.chance(0.2)) {
      return this.atom();
    }
    const d = depth - 1;
    return this.pick([
      () => [...this.expr(d), this.pick(BINARY), ...this.expr(d)],
      () => [...this.expr(d), this.pick(BINARY), ...this.expr(d)],
      () => [this.pick(['!', '-', '+', '~', 'typeof', 'void']), ...this.expr(d)],
      () => [...this.expr(d), '?', ...this.expr(d), ':', ...this.expr(d)],
      () => [...this.target(d), this.pick(ASSIGN), ...this.expr(d)],
      () => [...this.expr(d), '.', this.pick(['p', 'length', 'default'])],
      () => [...this.expr(d), '[', ...this.expr(d), ']'],
      () => [...this.expr(d), '(', ...this.list(d), ')'],
      () => ['(', ...this.expr(d), ')'],
      () => ['(', ...this.expr(d), ')'],
      () => ['[', ...this.list(d), ']'],
      () => ['{', ...this.props(d), '}'],
      () => [this.pick(['++', '--']), ...this.target(d)],
      () => [...this.target(d), this.pick(['++', '--'])],
    ])();
  }

  private list(depth: number): Array<string> {
    const items: Array<string> = [];
    const count = Math.floor(this.next() * 3);
    for (let i = 0; i < count; i++) {
      if (i > 0) {
        items.push(',');
      }
      items.push(...this.expr(depth));
    }
    if (count > 0 && this.chance(0.2)) {
      items.push(',');
    }
    return items;
  }

  private props(depth: number): Array<string> {
    const items: Array<string> = [];
    const count = Math.floor(this.next() * 3);
    for (let i = 0; i < count; i++) {
      if (i > 0) {
        items.push(',');
      }
      if (this.chance(0.3)) {
        items.push(this.name());
      } else {
        items.push(this.pick(['k', 'default', "'s k'", '1', 'if']), ':', ...this.expr(depth));
      }
    }
    return items;
  }

  type(depth: number): Array<string> {
    if (depth <= 0 || this.chance(0.3)) {
      return [this.pick(['number', 'bigint', 'boolean', 'string', 'void', 'undefined', 'null', 'unknown', 'Item', "'a'", '1', 'true'])];
    }
    const d = depth - 1;
    return this.pick([
      () => [...this.type(d), '|', ...this.type(d)],
      () => ['|', ...this.type(d)],
      () => [...this.type(d), '[', ']'],
      () => ['(', ...this.type(d), ')'],
      () => [this.pick(['Array', 'ReadonlyArray', 'Map']), '<', ...this.type(d), '>'],
      () => ['Map', '<', ...this.type(d), ',', ...this.type(d), '>'],
    ])();
  }

  private end(): Array<string> {
    return this.chance(0.6) ? [';'] : [];
  }

  statement(depth: number, inLoop: boolean): Array<string> {
    const d = depth - 1;
    const choices: Array<() => Array<string>> = [
      () => [...this.expr(3), ...this.end()],
      () => [...this.expr(3), ...this.end()],
      () => ['let', this.name(), ...(this.chance(0.5) ? [':', ...this.type(2)] : []), '=', ...this.expr(2), ...this.end()],
      () => ['const', this.name(), '=', ...this.expr(2), ...this.end()],
      () => ['return', ...(this.chance(0.7) ? this.expr(2) : []), ...this.end()],
      () => [';'],
    ];
    if (depth > 0) {
      choices.push(
        () => ['if', '(', ...this.expr(2), ')', ...this.block(d, inLoop), ...(this.chance(0.5) ? ['else', ...this.block(d, inLoop)] : [])],
        () => ['if', '(', ...this.expr(2), ')', ...this.statement(d, inLoop)],
        () => ['while', '(', ...this.expr(2), ')', ...this.block(d, true)],
        () => ['for', '(', this.pick(['const', 'let']), 'v', 'of', ...this.expr(2), ')', ...this.block(d, true)],
        () => this.block(d, inLoop),
      );
    }
    if (inLoop) {
      choices.push(() => [this.pick(['break', 'continue']), ...this.end()]);
    }
    return this.pick(choices)();
  }

  private block(depth: number, inLoop: boolean): Array<string> {
    const body: Array<string> = ['{'];
    const count = Math.floor(this.next() * 3);
    for (let i = 0; i < count; i++) {
      body.push(...this.statement(depth, inLoop));
    }
    body.push('}');
    return body;
  }

  program(): string {
    const parts: Array<Array<string>> = [];
    if (this.chance(0.4)) {
      parts.push(['export', 'interface', 'Item', '{', 'readonly', 'id', ':', ...this.type(1), ';', 'count', '?', ':', ...this.type(2), '}']);
    }
    if (this.chance(0.3)) {
      parts.push(['type', 'T', '=', ...this.type(3), ...this.end()]);
    }
    parts.push([
      ...(this.chance(0.5) ? ['export'] : []),
      'function',
      'f',
      '(',
      'a',
      ':',
      ...this.type(2),
      ',',
      'b',
      ')',
      ':',
      ...this.type(2),
      ...this.block(3, false),
    ]);
    return parts.map((p) => this.join(p)).join('\n');
  }
}

const BINARY = ['??', '||', '&&', '|', '^', '&', '==', '!=', '===', '!==', '<', '>', '<=', '>=', 'in', 'instanceof', '<<', '>>', '>>>', '+', '-', '*', '/', '%', '**'];
const ASSIGN = ['=', '+=', '-=', '*=', '/=', '%=', '**=', '<<=', '>>=', '>>>=', '&=', '|=', '^=', '&&=', '||=', '??='];

function fuzz(count: number, seed: number): void {
  const dir = mkdtempSync(join(tmpdir(), 'tolean-fuzz-'));
  const tally = { equal: 0, bothRefuse: 0, conservative: 0 };
  const reasons = new Map<string, number>();
  for (let i = 0; i < count; i++) {
    const caseSeed = seed + i;
    const text = new Gen(caseSeed).program();
    const path = join(dir, `case${caseSeed}.ts`);
    writeFileSync(path, text);
    const expected = tscAst(path, text);
    const actual = lean(path);
    if (expected.kind === 'tree' && actual.kind === 'tree') {
      if (actual.sexp === expected.sexp) {
        tally.equal++;
      } else {
        failures.push(`fuzz seed ${caseSeed} (${path}): the trees differ at ${firstDifference(actual.sexp, expected.sexp)}`);
      }
    } else if (expected.kind === 'refused' && actual.kind === 'refused') {
      tally.bothRefuse++;
      reasons.set(expected.reason, (reasons.get(expected.reason) ?? 0) + 1);
    } else if (actual.kind === 'refused' && actual.message.includes(CONSERVATIVE)) {
      tally.conservative++;
    } else if (actual.kind === 'refused') {
      failures.push(`fuzz seed ${caseSeed} (${path}): only the Lean parser refuses it: ${actual.message}`);
    } else if (expected.kind === 'refused') {
      failures.push(`fuzz seed ${caseSeed} (${path}): only the reference refuses it: ${expected.reason}`);
    }
  }
  console.log(
    `fuzz: ${count} programs from seed ${seed}: ${tally.equal} equal trees, ` +
      `${tally.bothRefuse} refused by both, ${tally.conservative} refused only for a tsc lookalike`,
  );
  const top = [...reasons].sort((x, y) => y[1] - x[1]).slice(0, 5);
  console.log(`most common reasons to refuse: ${top.map(([r, n]) => `${n}× ${r}`).join('; ')}`);
}

function flag(name: string): number | undefined {
  const i = process.argv.indexOf(name);
  const value = i < 0 ? undefined : process.argv[i + 1];
  return value === undefined ? undefined : Number(value);
}

const accept = corpus('corpus/parse/accept');
const reject = corpus('corpus/parse/reject');
accept.forEach(checkAccept);
reject.forEach(checkReject);
console.log(`corpus: ${accept.length} accepted files, ${reject.length} refused files`);
fuzz(flag('--fuzz') ?? 500, flag('--seed') ?? Math.floor(Math.random() * 1e9));

for (const f of failures) {
  console.error(`FAIL ${f}`);
}
process.exit(failures.length === 0 ? 0 : 1);
