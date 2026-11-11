/**
 * The interpreter of `tolean/TypeScript/Spec/Eval.lean` against Node, on
 * random programs.
 *
 * Every certificate and `program_sound` hold relative to the interpreter, so it
 * is trusted. This test is evidence that it means what JavaScript means. It
 * runs random programs of the subset (`gen.ts`) with random arguments in the
 * interpreter, through `tolean interpret`, and in Node, and requires two
 * things:
 *
 * - When the interpreter gives a value, Node returns the same value. This
 *   holds for every program that the parser accepts, in the subset or not,
 *   except for one gap that the plan for pure TypeScript lists and the
 *   random programs do not reach: an assignment to the variable of a
 *   `for (const x of xs)` loop.
 * - When the interpreter says that a call throws a value, Node throws the
 *   same value. An `Error` compares by its class and its message.
 * - When the translator accepts the program and the interpreter gives no
 *   value, Node throws.
 *
 * The parser accepts some programs that Node does not load, because they break
 * an early error rule of ECMA-262, such as a name declared twice in a block.
 * The interpreter does not check those rules, so the test skips such a
 * program, but the translator must refuse it.
 *
 * Numbers compare by their 64 bits, so `-0` and `0` differ, and every `NaN` is
 * the same value. `nix run .#test-engines` runs this file on every maintained
 * Node release line. Set `TOLEAN_SEED` to repeat a run, and `TOLEAN_PROGRAMS`
 * to run more programs. The interpreter is `.lake/build/bin/tolean`, or
 * `$TOLEAN`.
 */
import { expect, test } from 'vitest';

import { spawnSync } from 'node:child_process';
import { mkdtempSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import fc from 'fast-check';
import ts from 'typescript';

import { Gen, type Signatures, type Ty } from './gen.ts';

const root = fileURLToPath(new URL('../../', import.meta.url));
const tolean = process.env.TOLEAN ?? join(root, '.lake/build/bin/tolean');
const seed = Number(process.env.TOLEAN_SEED ?? Math.floor(Math.random() * 1e9));
const programCount = Number(process.env.TOLEAN_PROGRAMS ?? 1000);
const callsPerFunction = 5;

/** A value as `tolean interpret` writes it (see `Interpret.lean`). */
type Value =
  | { bigint: string }
  | { number: string }
  | boolean
  | string
  | null
  | { undefined: true }
  | Array<Value>
  | { object: Array<[string, Value]> }
  | { error: [string, Array<[string, Value]>] };

const bitsOf = (x: number): string => {
  const view = new DataView(new ArrayBuffer(8));
  view.setFloat64(0, x);
  return view.getBigUint64(0).toString();
};

const ofBits = (bits: string): number => {
  const view = new DataView(new ArrayBuffer(8));
  view.setBigUint64(0, BigInt(bits));
  return view.getFloat64(0);
};

function encode(x: unknown): Value {
  switch (typeof x) {
    case 'bigint':
      return { bigint: x.toString() };
    case 'number':
      return { number: bitsOf(x) };
    case 'boolean':
    case 'string':
      return x;
    case 'undefined':
      return { undefined: true };
    case 'object':
      if (x === null) return null;
      if (Array.isArray(x)) return x.map(encode);
      return { object: Object.entries(x).map(([k, v]): [string, Value] => [k, encode(v)]) };
    default:
      throw new Error(`no value of the subset: ${String(x)}`);
  }
}

function decode(v: Value): unknown {
  if (v === null || typeof v === 'boolean' || typeof v === 'string') return v;
  if (Array.isArray(v)) return v.map(decode);
  if ('undefined' in v) return undefined;
  if ('bigint' in v) return BigInt(v.bigint);
  if ('number' in v) return ofBits(v.number);
  if ('error' in v) throw new Error('an error object is never an argument');
  return Object.fromEntries(v.object.map(([k, x]) => [k, decode(x)]));
}

/** `v` as text, with every `NaN` written the same way. */
function canonical(v: Value): string {
  const strip = (w: Value): unknown => {
    if (w === null || typeof w === 'boolean' || typeof w === 'string') return w;
    if (Array.isArray(w)) return w.map(strip);
    if ('number' in w) return { number: Number.isNaN(ofBits(w.number)) ? 'NaN' : w.number };
    if ('bigint' in w || 'undefined' in w) return w;
    if ('error' in w) return { error: [w.error[0], w.error[1].map(([k, x]) => [k, strip(x)])] };
    return { object: w.object.map(([k, x]) => [k, strip(x)]) };
  };
  return JSON.stringify(strip(v));
}

// Edges first: zeros, the ends of the safe range and past them, and the
// special values.
const bigints = fc.oneof(
  fc.constantFrom(0n, 1n, -1n, 7n, 2n ** 53n, -(2n ** 64n) + 1n),
  fc.bigInt({ min: -(2n ** 70n), max: 2n ** 70n }),
);
const numbers = fc.oneof(
  fc.constantFrom(0, -0, 1, -1, 0.5, -2.5, 2 ** 53 - 1, 2 ** 53, 2 ** 53 + 2, 1e308, -1e308, 5e-324, NaN, Infinity, -Infinity),
  fc.integer({ min: -1000, max: 1000 }),
  fc.double(),
);

function arbitrary(t: Ty, sig: Signatures): fc.Arbitrary<unknown> {
  switch (t.k) {
    case 'bigint':
      return bigints;
    case 'number':
      return numbers;
    case 'boolean':
      return fc.boolean();
    case 'string':
      return fc.oneof(fc.constantFrom('', 'a', 'ab', 'é', '😀', '\uFFFF'), fc.string({ unit: 'grapheme', maxLength: 4 }));
    case 'nullable':
      return fc.option(arbitrary(t.of, sig), { nil: null });
    case 'optional':
      return fc.option(arbitrary(t.of, sig), { nil: undefined });
    case 'array':
      return fc.array(arbitrary(t.of, sig), { maxLength: 3 });
    case 'struct': {
      const fields = sig.structs.find((s) => s.name === t.name)?.fields ?? [];
      // A tuple, so that the object has its fields in the interface's order.
      return fc
        .tuple(...fields.map(([, ty]) => arbitrary(ty, sig)))
        .map((values) => Object.fromEntries(fields.map(([f], i) => [f, values[i]])));
    }
  }
}

type Call = { function: string; args: Array<Value> };
type Program = { seed: number; source: string; calls: Array<Call> };
/** A result is `null` when the interpreter gives no value. */
type Interpreted =
  | { parsed: false }
  | { parsed: true; accepted: boolean; results: Array<{ value: Value } | { throws: Value } | null> };
type NodeResult = { returns: unknown } | { throws: string; thrown: unknown };

/** What Node threw, as `tolean interpret` writes it: an `Error` as its class
 * and its message, and any other value as itself. */
function shownThrow(x: unknown): string {
  if (x instanceof Error) return JSON.stringify({ error: [x.name, [['message', x.message]]] });
  return shown(x);
}

/** `x` as text, or why it is no value of the subset. */
function shown(x: unknown): string {
  try {
    return canonical(encode(x));
  } catch (e) {
    return e instanceof Error ? e.message : String(e);
  }
}

test(`the interpreter agrees with Node ${process.version} on random programs`, async () => {
  // First, so that the seed shows when a step below fails.
  console.log(`interpreter: ${programCount} programs from seed ${seed} on Node ${process.version}`);
  const programs: Array<Program> = [];
  for (let i = 0; i < programCount; i++) {
    // The program and its arguments come from its own seed only, so
    // `TOLEAN_SEED=<that seed>` repeats both.
    const programSeed = seed + i;
    const gen = new Gen(programSeed);
    const source = gen.program();
    const sig = gen.signatures();
    const calls = sig.functions.flatMap((f, j) =>
      fc
        .sample(fc.tuple(...f.params.map((p) => arbitrary(p, sig))), { numRuns: callsPerFunction, seed: programSeed * 7 + j })
        .map((args) => ({ function: f.name, args: args.map(encode) })),
    );
    programs.push({ seed: programSeed, source, calls });
  }

  // A few hundred programs at a time, so that no pipe holds a large input.
  const interpreted: Array<Interpreted> = [];
  for (let start = 0; start < programs.length; start += 500) {
    const batch = programs.slice(start, start + 500).map(({ source, calls }) => ({ source, calls }));
    const run = spawnSync(tolean, ['interpret'], { input: JSON.stringify({ programs: batch }), encoding: 'utf8', maxBuffer: 1 << 28 });
    expect(run.status, run.stderr).toBe(0);
    interpreted.push(...(JSON.parse(run.stdout) as { programs: Array<Interpreted> }).programs);
  }

  const dir = mkdtempSync(join(tmpdir(), 'tolean-interpreter-'));
  const failures: Array<string> = [];
  const tally = { parsed: 0, accepted: 0, unloaded: 0, values: 0, throws: 0 };
  for (const [i, program] of programs.entries()) {
    const lean = interpreted[i];
    if (lean === undefined || !lean.parsed) continue;
    tally.parsed++;
    if (lean.accepted) tally.accepted++;
    const path = join(dir, `case${program.seed}.mjs`);
    const js = ts.transpileModule(program.source, {
      compilerOptions: { target: ts.ScriptTarget.ESNext, module: ts.ModuleKind.ESNext },
    }).outputText;
    writeFileSync(path, js);
    writeFileSync(join(dir, `case${program.seed}.ts`), program.source);
    let mod: Record<string, (...args: Array<unknown>) => unknown>;
    try {
      mod = (await import(pathToFileURL(path).href)) as typeof mod;
    } catch (e) {
      tally.unloaded++;
      if (lean.accepted) {
        failures.push(`seed ${program.seed} (${join(dir, `case${program.seed}.ts`)}): the translator accepts a program that Node does not load: ${String(e)}`);
      }
      continue;
    }
    for (const [j, call] of program.calls.entries()) {
      const expected = lean.results[j] ?? null;
      const where = `seed ${program.seed} (${join(dir, `case${program.seed}.ts`)}): ${call.function}(${JSON.stringify(call.args)})`;
      const fn = mod[call.function];
      if (typeof fn !== 'function') {
        failures.push(`${where}: Node's module exports no function ${call.function}`);
        continue;
      }
      // Only the call is in the `try`, so that a throw is Node's.
      let actual: NodeResult;
      try {
        actual = { returns: fn(...call.args.map(decode)) };
      } catch (e) {
        actual = { throws: e instanceof Error ? e.name : String(e), thrown: e };
      }
      if (expected !== null && 'throws' in expected) {
        tally.throws++;
        if ('returns' in actual) {
          failures.push(`${where}: the interpreter throws ${canonical(expected.throws)}, Node ${shown(actual.returns)}`);
        } else if (shownThrow(actual.thrown) !== canonical(expected.throws)) {
          failures.push(`${where}: the interpreter throws ${canonical(expected.throws)}, Node throws ${shownThrow(actual.thrown)}`);
        }
      } else if (expected !== null) {
        tally.values++;
        if (!('returns' in actual)) {
          failures.push(`${where}: the interpreter gives ${canonical(expected.value)}, Node throws ${actual.throws}`);
        } else if (shown(actual.returns) !== canonical(expected.value)) {
          failures.push(`${where}: the interpreter gives ${canonical(expected.value)}, Node ${shown(actual.returns)}`);
        }
      } else if (lean.accepted) {
        tally.throws++;
        if ('returns' in actual) {
          failures.push(`${where}: the interpreter gives no value, Node ${shown(actual.returns)}`);
        }
      }
    }
  }
  console.log(
    `interpreter: ${tally.parsed} parsed, ${tally.accepted} translated, ${tally.unloaded} that Node does not load; ` +
      `${tally.values} calls with a value, ${tally.throws} that throw`,
  );
  expect(failures).toEqual([]);
}, 600_000);

// A parameter that a call leaves out is `undefined`, both for a call inside
// the program and for the call that runs it, as in Node.
test('the interpreter binds a parameter that a call leaves out to undefined', async () => {
  const cases: Array<{ source: string; args: Array<unknown> }> = [
    { source: 'export function f(a: bigint, b?: bigint): bigint { return a + (b ?? 10n); }', args: [1n] },
    {
      source:
        'function h(a: bigint, b?: bigint): bigint { if (b === undefined) { return a; } return a + b; }\n' +
        'export function f(a: bigint): bigint { return h(a) + h(a, 2n) + h(a, undefined); }',
      args: [3n],
    },
    { source: 'export function f(a?: boolean): boolean { return a !== undefined; }', args: [] },
    { source: 'export function f(a?: number): number | null { return a ?? null; }', args: [] },
  ];
  const input = {
    programs: cases.map(({ source, args }) => ({ source, calls: [{ function: 'f', args: args.map(encode) }] })),
  };
  const run = spawnSync(tolean, ['interpret'], { input: JSON.stringify(input), encoding: 'utf8' });
  expect(run.status, run.stderr).toBe(0);
  const results = (JSON.parse(run.stdout) as { programs: Array<Interpreted> }).programs;
  const dir = mkdtempSync(join(tmpdir(), 'tolean-optional-'));
  for (const [i, { source, args }] of cases.entries()) {
    const lean = results[i];
    expect(lean?.parsed, source).toBe(true);
    if (lean === undefined || !lean.parsed) continue;
    const path = join(dir, `case${i}.mjs`);
    writeFileSync(path, ts.transpileModule(source, { compilerOptions: { target: ts.ScriptTarget.ESNext, module: ts.ModuleKind.ESNext } }).outputText);
    const mod = (await import(pathToFileURL(path).href)) as { f: (...a: Array<unknown>) => unknown };
    const value = lean.results[0]?.value;
    expect(value === undefined ? 'no value' : canonical(value), source).toBe(canonical(encode(mod.f(...args))));
  }
});

// An assignment to a `const` throws a `TypeError` in Node, so the interpreter
// must give no value for it, whatever the operator.
test('the interpreter gives no value where an assignment to a const throws', async () => {
  const sources = [
    'export function f(): bigint | null { const x: bigint | null = null; x ??= 1n; return x; }',
    'export function f(): bigint { const x = 1n; x = 2n; return x; }',
    'export function f(): bigint { const x = 1n; x += 2n; return x; }',
    'export function f(): bigint { const x = 1n; x++; return x; }',
    'export function f(b: boolean): bigint { const x = 1n; if (b) { x = 2n; } return x; }',
  ];
  const input = { programs: sources.map((source) => ({ source, calls: [{ function: 'f', args: [true] }] })) };
  const run = spawnSync(tolean, ['interpret'], { input: JSON.stringify(input), encoding: 'utf8' });
  expect(run.status, run.stderr).toBe(0);
  const results = (JSON.parse(run.stdout) as { programs: Array<Interpreted> }).programs;
  const dir = mkdtempSync(join(tmpdir(), 'tolean-const-'));
  for (const [i, source] of sources.entries()) {
    const lean = results[i];
    expect(lean?.parsed, source).toBe(true);
    if (lean === undefined || !lean.parsed) continue;
    expect(lean.results[0] ?? null, source).toBeNull();
    const path = join(dir, `case${i}.mjs`);
    writeFileSync(path, ts.transpileModule(source, { compilerOptions: { target: ts.ScriptTarget.ESNext, module: ts.ModuleKind.ESNext } }).outputText);
    const mod = (await import(pathToFileURL(path).href)) as { f: (b: boolean) => unknown };
    expect(() => mod.f(true), source).toThrow(TypeError);
  }
});

// A JS loop over a set, a map or an array sees a change that its body makes
// to what it runs over, and the interpreter takes the values when the loop
// starts. So it must give no value for such a loop, however the iterable
// reaches the collection. A loop over a copy, `new Set(s)`, runs over a new
// set, so a change to `s` does not reach it, and there the interpreter must
// agree with Node.
test('the interpreter gives no value for a loop that changes what it runs over', async () => {
  const start = 'const s = new Set<bigint>(); s.add(1n); s.add(2n); let n = 0n;';
  const loop = (iterable: string) =>
    `export function f(b: boolean): bigint { ${start} for (const x of ${iterable}) { s.delete(2n); n += x; } return n; }`;
  const changing = [
    loop('s'),
    loop('(s)'),
    loop('((s))'),
    loop('s satisfies ReadonlySet<bigint>'),
    loop('b ? s : new Set<bigint>()'),
    // A new map holds `s` as a value, and `get` gives it back.
    loop('new Map<bigint, Set<bigint>>([[0n, s]]).get(0n) ?? new Set<bigint>()'),
    'export function f(b: boolean): bigint { const m = new Map<bigint, bigint>(); m.set(1n, 1n); m.set(2n, 2n); ' +
      'let n = 0n; for (const e of (m)) { m.delete(2n); n += e[1]; } return n; }',
  ];
  const copying = [loop('new Set<bigint>(s)'), loop('(new Set<bigint>(s))')];
  const sources = [...changing, ...copying];
  const input = { programs: sources.map((source) => ({ source, calls: [{ function: 'f', args: [true] }] })) };
  const run = spawnSync(tolean, ['interpret'], { input: JSON.stringify(input), encoding: 'utf8' });
  expect(run.status, run.stderr).toBe(0);
  const results = (JSON.parse(run.stdout) as { programs: Array<Interpreted> }).programs;
  const dir = mkdtempSync(join(tmpdir(), 'tolean-iterable-'));
  for (const [i, source] of sources.entries()) {
    const lean = results[i];
    expect(lean?.parsed, source).toBe(true);
    if (lean === undefined || !lean.parsed) continue;
    if (i < changing.length) {
      expect(lean.results[0] ?? null, source).toBeNull();
      continue;
    }
    const path = join(dir, `case${i}.mjs`);
    writeFileSync(path, ts.transpileModule(source, { compilerOptions: { target: ts.ScriptTarget.ESNext, module: ts.ModuleKind.ESNext } }).outputText);
    const mod = (await import(pathToFileURL(path).href)) as { f: (b: boolean) => unknown };
    const value = lean.results[0]?.value;
    expect(value === undefined ? 'no value' : canonical(value), source).toBe(canonical(encode(mod.f(true))));
  }
});

// The spec holds an array, a map or a set as a value, which is the JS meaning
// only when nothing else holds the object while it changes. So it must give
// no value for a function that changes a collection that another name, a
// parameter, a loop variable or an object may hold, and agree with Node for
// one that it owns.
test('the interpreter gives no value where a changed collection has another holder', async () => {
  // Each result is read through a loop, `has` or an index, which the
  // interpreter has rules for, so the only reason for no value is the check.
  const sum = 'function sum(a: ReadonlyArray<bigint>): bigint { let t = 0n; for (const v of a) { t += v; } return t; }\n';
  const shared = [
    'export function f(b: boolean): boolean { const m = new Map<bigint, bigint>(); const n = m; ' +
      'm.set(1n, 2n); return n.has(1n); }',
    sum + 'export function f(b: boolean): bigint { const xs: Array<bigint> = [0n]; const ys = xs; xs.push(1n); return sum(ys); }',
    'function g(s: Set<bigint>): boolean { s.add(1n); return true; }\n' +
      'export function f(b: boolean): boolean { const s = new Set<bigint>(); const z = g(s); return s.has(1n); }',
    sum + 'export function f(b: boolean): bigint { const xs: Array<Array<bigint>> = [[]]; ' +
      'for (const x of xs) { x.push(1n); } return sum(xs[0]); }',
    'export function f(b: boolean): boolean { const m = new Map<bigint, bigint>(); const o = { m }; ' +
      'm.set(1n, 1n); return o.m.has(1n); }',
  ];
  const owned = [
    sum + 'export function f(b: boolean): bigint { const xs: Array<bigint> = [1n]; xs.push(2n); return sum(xs); }',
    'export function f(b: boolean): boolean { const m = new Map<bigint, bigint>(); m.set(1n, 2n); m.delete(3n); ' +
      'return m.has(1n); }',
    'export function f(b: boolean): boolean { const s = new Set<bigint>(); s.add(1n); const t = new Set<bigint>(s); ' +
      's.add(2n); return t.has(2n); }',
  ];
  const sources = [...shared, ...owned];
  const input = { programs: sources.map((source) => ({ source, calls: [{ function: 'f', args: [true] }] })) };
  const run = spawnSync(tolean, ['interpret'], { input: JSON.stringify(input), encoding: 'utf8' });
  expect(run.status, run.stderr).toBe(0);
  const results = (JSON.parse(run.stdout) as { programs: Array<Interpreted> }).programs;
  const dir = mkdtempSync(join(tmpdir(), 'tolean-owned-'));
  for (const [i, source] of sources.entries()) {
    const lean = results[i];
    expect(lean?.parsed, source).toBe(true);
    if (lean === undefined || !lean.parsed) continue;
    if (i < shared.length) {
      expect(lean.results[0] ?? null, source).toBeNull();
      continue;
    }
    const path = join(dir, `case${i}.mjs`);
    writeFileSync(path, ts.transpileModule(source, { compilerOptions: { target: ts.ScriptTarget.ESNext, module: ts.ModuleKind.ESNext } }).outputText);
    const mod = (await import(pathToFileURL(path).href)) as { f: (b: boolean) => unknown };
    const value = lean.results[0]?.value;
    expect(value === undefined ? 'no value' : canonical(value), source).toBe(canonical(encode(mod.f(true))));
  }
});
