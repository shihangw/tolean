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
 *   except for three gaps that the random programs do not reach. The first,
 *   which the plan for pure TypeScript lists, is an assignment to the
 *   variable of a `for (const x of xs)` loop. The second is a call of a local
 *   function before its declaration, where a function of the module has the
 *   same name: JS binds the local function when its block starts, but the
 *   interpreter binds it where the declaration stands, so the call runs the
 *   function of the module. The third is a declaration, between a local
 *   function and a call of it, that hides a name the local function reads:
 *   JS keeps the variable of the declaration, and the interpreter takes the
 *   one in scope at the call. The translator refuses all three.
 * - When the interpreter says that a call throws a value, Node throws the
 *   same value. An `Error` compares by its class and its message.
 * - When the translator accepts the program and the interpreter gives no
 *   value, Node throws. A program that sorts by a `number` key is the
 *   exception: its comparator is consistent only when no key is `NaN`, and a
 *   difference only when every key is finite, so the interpreter gives no
 *   value on other arrays, where Node returns one. The translation makes no
 *   claim there.
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
import { mkdtempSync, readFileSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import fc from 'fast-check';
import ts from 'typescript';

import { Gen, type Signatures, type Ty } from './gen.ts';
import { dateParseCases } from './dateParseCases.ts';
import { checkRegexpModel } from './regexpModel.ts';

const root = fileURLToPath(new URL('../../', import.meta.url));
const tolean = process.env.TOLEAN ?? join(root, '.lake/build/bin/tolean');
const seed = Number(process.env.TOLEAN_SEED ?? Math.floor(Math.random() * 1e9));
const programCount = Number(process.env.TOLEAN_PROGRAMS ?? 1000);
const callsPerFunction = 5;

test('the flagless RegExp parser and matcher agree with Node on patterns and UTF-16 inputs', () => {
  checkRegexpModel(seed);
}, 200_000);

/** A value as `tolean interpret` writes it (see `Interpret.lean`). */
type Value =
  | { bigint: string }
  | { number: string }
  | boolean
  | string
  | null
  | { undefined: true }
  /** A string that holds a lone surrogate, as its UTF-16 code units. A JSON
   * string cannot hold one exactly, so the interpreter writes it this way. */
  | { utf16: Array<number> }
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
      return x;
    case 'string':
      return x.isWellFormed() ? x : { utf16: Array.from({ length: x.length }, (_, i) => x.charCodeAt(i)) };
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
  if ('utf16' in v) return String.fromCharCode(...v.utf16);
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
    if ('bigint' in w || 'undefined' in w || 'utf16' in w) return w;
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
      return fc.oneof(fc.constantFrom('', 'a', 'ab', 'é', '😀', '\uFFFF', ' a,b ', '\u00A0x\u2028', ','), fc.string({ unit: 'grapheme', maxLength: 4 }));
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
type Program = { seed: number; source: string; calls: Array<Call>; sortsByNumber: boolean };
/** A result is `null` when the interpreter gives no value. */
type Interpreted =
  | { parsed: false }
  | { parsed: true; accepted: boolean; results: Array<{ value: Value } | { throws: Value } | null> };
type NodeResult = { returns: unknown } | { throws: string; thrown: unknown };

/** What Node threw, as `tolean interpret` writes it: an `Error` as its class,
 * its message and its own enumerable properties, which are the fields of an
 * error class, and any other value as itself. */
function shownThrow(x: unknown): string {
  if (x instanceof Error) {
    const fields: Array<[string, Value]> = [
      ['message', encode(x.message)],
      ...Object.entries(x).map(([k, v]): [string, Value] => [k, encode(v)]),
    ];
    return canonical({ error: [x.constructor.name, fields] });
  }
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

test('certified local functions agree with Node on random arguments', async () => {
  const source = ['localFunctionCertificate', 'localFunctionLoopCertificates'].map(name =>
    readFileSync(new URL(`./corpus/translate/accept/${name}.ts`, import.meta.url), 'utf8')).join('\n');
  const inputs = fc.sample(fc.tuple(fc.bigInt(), fc.bigInt()), { seed, numRuns: 50 });
  const calls = inputs.flatMap(([start, amount]) => [
    { function: 'tally', args: [encode(start), encode(amount)] },
    { function: 'twice', args: [encode([start, amount])] },
    { function: 'localLoopSum', args: [encode([start, amount]), encode(amount)] },
    { function: 'localLoopUpdate', args: [encode([start, amount])] },
    { function: 'localLoopNested', args: [encode([start, amount])] },
  ]);
  const run = spawnSync(tolean, ['interpret'], {
    input: JSON.stringify({ programs: [{ source, calls }] }), encoding: 'utf8',
  });
  expect(run.status, run.stderr).toBe(0);
  const result = (JSON.parse(run.stdout) as { programs: Array<Interpreted> }).programs[0];
  expect(result?.parsed).toBe(true);
  if (!result?.parsed) return;
  expect(result.accepted).toBe(true);
  const dir = mkdtempSync(join(tmpdir(), 'tolean-local-certificate-'));
  const path = join(dir, 'local.mjs');
  writeFileSync(path, ts.transpileModule(source, {
    compilerOptions: { target: ts.ScriptTarget.ESNext, module: ts.ModuleKind.ESNext },
  }).outputText);
  const mod = await import(pathToFileURL(path).href) as {
    tally: (start: bigint, amount: bigint) => bigint;
    twice: (xs: Array<bigint>) => Array<bigint>;
    localLoopSum: (xs: Array<bigint>, fee: bigint) => bigint;
    localLoopUpdate: (xs: Array<bigint>) => bigint;
    localLoopNested: (xs: Array<bigint>) => bigint;
  };
  for (const [i, [start, amount]] of inputs.entries()) {
    expect(result.results[5 * i]).toEqual({ value: encode(mod.tally(start, amount)) });
    expect(result.results[5 * i + 1]).toEqual({ value: encode(mod.twice([start, amount])) });
    expect(result.results[5 * i + 2]).toEqual({ value: encode(mod.localLoopSum([start, amount], amount)) });
    expect(result.results[5 * i + 3]).toEqual({ value: encode(mod.localLoopUpdate([start, amount])) });
    expect(result.results[5 * i + 4]).toEqual({ value: encode(mod.localLoopNested([start, amount])) });
  }
});

test('local returns and sibling calls preserve captured state and agree with Node', async () => {
  const source = ['localFunctionReturnsAndChanges', 'localFunctionSiblingCalls'].map(name =>
    readFileSync(new URL(`./corpus/translate/accept/${name}.ts`, import.meta.url), 'utf8')).join('\n');
  const inputs = fc.sample(fc.tuple(fc.bigInt(), fc.bigInt()), { seed, numRuns: 50 });
  const calls = inputs.flatMap(([start, amount]) => [
    { function: 'f', args: [encode(start)] },
    { function: 'tally', args: [encode(start), encode(amount)] },
    { function: 'returnCall', args: [encode(start), encode(amount)] },
    { function: 'loopCalls', args: [encode([start, amount])] },
    { function: 'capturedTotal', args: [encode([start, amount])] },
    { function: 'calculate', args: [encode(start)] },
    { function: 'accumulate', args: [encode([start, amount])] },
    { function: 'captured', args: [encode(start), encode(amount)] },
    { function: 'siblingState', args: [encode(start), encode(amount)] },
  ]);
  const run = spawnSync(tolean, ['interpret'], {
    input: JSON.stringify({ programs: [{ source, calls }] }), encoding: 'utf8',
  });
  expect(run.status, run.stderr).toBe(0);
  const result = (JSON.parse(run.stdout) as { programs: Array<Interpreted> }).programs[0];
  expect(result?.parsed).toBe(true);
  if (!result?.parsed) return;
  expect(result.accepted).toBe(true);
  const dir = mkdtempSync(join(tmpdir(), 'tolean-local-return-state-'));
  const path = join(dir, 'local.mjs');
  writeFileSync(path, ts.transpileModule(source, {
    compilerOptions: { target: ts.ScriptTarget.ESNext, module: ts.ModuleKind.ESNext },
  }).outputText);
  const mod = await import(pathToFileURL(path).href) as {
    f: (x: bigint) => bigint;
    tally: (start: bigint, amount: bigint) => bigint;
    returnCall: (start: bigint, amount: bigint) => bigint;
    loopCalls: (xs: Array<bigint>) => bigint;
    capturedTotal: (xs: Array<bigint>) => bigint;
    calculate: (x: bigint) => bigint;
    accumulate: (xs: Array<bigint>) => bigint;
    captured: (factor: bigint, x: bigint) => bigint;
    siblingState: (start: bigint, amount: bigint) => bigint;
  };
  for (const [i, [start, amount]] of inputs.entries()) {
    expect(result.results[9 * i]).toEqual({ value: encode(mod.f(start)) });
    expect(result.results[9 * i + 1]).toEqual({ value: encode(mod.tally(start, amount)) });
    expect(result.results[9 * i + 2]).toEqual({ value: encode(mod.returnCall(start, amount)) });
    expect(result.results[9 * i + 3]).toEqual({ value: encode(mod.loopCalls([start, amount])) });
    expect(result.results[9 * i + 4]).toEqual({ value: encode(mod.capturedTotal([start, amount])) });
    expect(result.results[9 * i + 5]).toEqual({ value: encode(mod.calculate(start)) });
    expect(result.results[9 * i + 6]).toEqual({ value: encode(mod.accumulate([start, amount])) });
    expect(result.results[9 * i + 7]).toEqual({ value: encode(mod.captured(start, amount)) });
    expect(result.results[9 * i + 8]).toEqual({ value: encode(mod.siblingState(start, amount)) });
  }
});

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
    programs.push({ seed: programSeed, source, calls, sortsByNumber: gen.sortsByNumber });
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
      } else if (lean.accepted && !program.sortsByNumber) {
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

test('predicate annotations do not change what a guard computes', async () => {
  const bodies = [
    'return value.kind === "circle";',
    'return true;',
    'if (value.kind === "circle") { return value.radius > 0n; } return false;',
    'if (value.kind === "circle") { return true; } else { return false; }',
  ];
  const args = fc.sample(fc.oneof(
    bigints.map((radius) => ({ kind: 'circle', radius })),
    bigints.map((side) => ({ kind: 'square', side })),
  ), { seed, numRuns: 100 });
  const sources = bodies.map((body) => `
    interface Circle { readonly kind: "circle"; readonly radius: bigint; }
    interface Square { readonly kind: "square"; readonly side: bigint; }
    type Shape = Circle | Square;
    export function guard(value: Shape): value is Circle { ${body} }
    export function caller(value: Shape): boolean {
      if (guard(value)) { return true; } else { return false; }
    }
  `);
  const calls = args.flatMap((arg) => ['guard', 'caller'].map((name) =>
    ({ function: name, args: [encode(arg)] })));
  const run = spawnSync(tolean, ['interpret'], {
    input: JSON.stringify({ programs: sources.map((source) => ({ source, calls })) }),
    encoding: 'utf8',
  });
  expect(run.status, run.stderr).toBe(0);
  const results = (JSON.parse(run.stdout) as { programs: Array<Interpreted> }).programs;
  const dir = mkdtempSync(join(tmpdir(), 'tolean-predicate-'));
  for (const [i, source] of sources.entries()) {
    const lean = results[i];
    expect(lean?.parsed, source).toBe(true);
    if (lean === undefined || !lean.parsed) continue;
    expect(lean.accepted, source).toBe(i === 0 || i === 3);
    const path = join(dir, `case${i}.mjs`);
    writeFileSync(path, ts.transpileModule(source, {
      compilerOptions: { target: ts.ScriptTarget.ESNext, module: ts.ModuleKind.ESNext },
    }).outputText);
    const mod = await import(pathToFileURL(path).href);
    for (const [j, arg] of args.entries()) {
      for (const [k, name] of ['guard', 'caller'].entries()) {
        const value = lean.results[2 * j + k]?.value;
        expect(value === undefined ? 'no value' : canonical(value), source)
          .toBe(canonical(encode(mod[name](arg))));
      }
    }
  }
});

test('checked guards narrow both branches, aliases, local calls, and tag chains', async () => {
  const templates = [
    { file: 'typeGuards', names: ['isCircle', 'isSquare', 'size', 'squareSize', 'circleValue', 'aliasSize'], three: false },
    { file: 'typeGuardsLocal', names: ['localSize', 'arrowSize'], three: false },
    { file: 'typeGuardsThree', names: ['size'], three: true },
  ];
  const generated = fc.sample(fc.tuple(fc.nat({ max: 10000 }), bigints, bigints, bigints), { seed, numRuns: 20 });
  const cases = templates.flatMap((template) => generated.map(([tag, radius, side, height]) => {
    const circle = `circle${tag}`;
    const square = `square${tag}`;
    const triangle = `triangle${tag}`;
    const source = readFileSync(new URL(`./corpus/translate/accept/${template.file}.ts`, import.meta.url), 'utf8')
      .replaceAll('"circle"', JSON.stringify(circle))
      .replaceAll('"square"', JSON.stringify(square))
      .replaceAll('"triangle"', JSON.stringify(triangle));
    const args: Array<unknown> = [{ kind: circle, radius }, { kind: square, side }];
    if (template.three) args.push({ kind: triangle, height });
    const calls: Array<{ name: string; arg: unknown }> =
      args.flatMap((arg) => template.names.map((name) => ({ name, arg })));
    if (template.file === 'typeGuards') {
      for (const arg of [circle, radius]) {
        calls.push({ name: 'isText', arg }, { name: 'text', arg });
      }
    }
    return { source, calls };
  }));
  const run = spawnSync(tolean, ['interpret'], {
    input: JSON.stringify({ programs: cases.map(({ source, calls }) => ({
      source, calls: calls.map(({ name, arg }) => ({ function: name, args: [encode(arg)] })),
    })) }),
    encoding: 'utf8',
    maxBuffer: 16 * 1024 * 1024,
  });
  expect(run.status, run.stderr).toBe(0);
  const results = (JSON.parse(run.stdout) as { programs: Array<Interpreted> }).programs;
  const dir = mkdtempSync(join(tmpdir(), 'tolean-checked-guard-'));
  for (const [i, { source, calls }] of cases.entries()) {
    const lean = results[i];
    expect(lean?.parsed, source).toBe(true);
    if (lean === undefined || !lean.parsed) continue;
    expect(lean.accepted, source).toBe(true);
    const path = join(dir, `case${i}.mjs`);
    writeFileSync(path, ts.transpileModule(source, {
      compilerOptions: { target: ts.ScriptTarget.ESNext, module: ts.ModuleKind.ESNext },
    }).outputText);
    const mod = await import(pathToFileURL(path).href);
    for (const [j, { name, arg }] of calls.entries()) {
      const value = lean.results[j]?.value;
      expect(value === undefined ? 'no value' : canonical(value), `${source}\n${name}`)
        .toBe(canonical(encode(mod[name](arg))));
    }
  }
});

test('type re-exports introduce no runtime binding', async () => {
  const source = 'export type { Point } from "./origin.ts"; export function f(n: bigint): bigint { return n + 1n; }';
  const input = { programs: [{ source, calls: [{ function: 'f', args: [encode(4n)] }] }] };
  const run = spawnSync(tolean, ['interpret'], { input: JSON.stringify(input), encoding: 'utf8' });
  expect(run.status, run.stderr).toBe(0);
  const result = (JSON.parse(run.stdout) as { programs: Array<Interpreted> }).programs[0];
  expect(result?.parsed).toBe(true);
  if (result === undefined || !result.parsed) return;
  const dir = mkdtempSync(join(tmpdir(), 'tolean-type-reexport-'));
  writeFileSync(join(dir, 'origin.ts'), 'export interface Point { readonly x: bigint }');
  const path = join(dir, 'barrel.mjs');
  writeFileSync(path, ts.transpileModule(source, { compilerOptions: { target: ts.ScriptTarget.ES2022, module: ts.ModuleKind.ESNext } }).outputText);
  const mod = await import(pathToFileURL(path).href) as { f: (n: bigint) => bigint };
  const value = result.results[0]?.value;
  expect(value === undefined ? 'no value' : canonical(value)).toBe(canonical(encode(mod.f(4n))));
});

test('the interpreter reads comparisons separated by expression operators as Node does', async () => {
  const sources = [
    'export function f(a: number, b: number, c: number, d: number): boolean { return a < b && c > d; }',
    'export function f(a: number, b: number, c: number, d: number): boolean { return a < b || c > d; }',
    'export function f(x: number, n: number): boolean { return x < n && n > 0; }',
    'export function f(p: boolean, q: number, r: number, s: number, u: number): boolean { return p === q < r === s > u; }',
    ...['===', '!=='].map(
      (op) => `export function f(a: number, b: number, c: number, d: number) { return a < b ${op} c > d; }`,
    ),
    ...['+', '*', '/'].map(
      (op) => `export function f(a: number, b: number, c: number, d: number) { return a < b ${op} c === d > 0; }`,
    ),
  ];
  const inputs = [[1, 2, 4, 3, 2], [2, 1, 4, 3, 4], [1, 2, 3, 4, 5], [NaN, 2, 4, 3, 0], [1, Infinity, 4, 3, 1]];
  const argumentsFor = (i: number, args: Array<number>): Array<number | boolean> =>
    i === 3 ? [args[0] === 1, ...args.slice(1)] : args.slice(0, i === 2 ? 2 : 4);
  const dir = mkdtempSync(join(tmpdir(), 'tolean-comparisons-'));
  const paths = sources.map((source, i) => {
    const path = join(dir, `case${i}.ts`);
    writeFileSync(path, source);
    return path;
  });
  const program = ts.createProgram(paths, {
    target: ts.ScriptTarget.ES2024, noEmit: true, strict: true, types: [], skipLibCheck: true,
  });
  expect(ts.getPreEmitDiagnostics(program).map((d) => ts.flattenDiagnosticMessageText(d.messageText, '\n'))).toEqual([]);
  const input = {
    programs: sources.map((source, i) => ({
      source,
      calls: inputs.map((args) => ({ function: 'f', args: argumentsFor(i, args).map(encode) })),
    })),
  };
  const run = spawnSync(tolean, ['interpret'], { input: JSON.stringify(input), encoding: 'utf8' });
  expect(run.status, run.stderr).toBe(0);
  const results = (JSON.parse(run.stdout) as { programs: Array<Interpreted> }).programs;
  for (const [i, source] of sources.entries()) {
    const lean = results[i];
    expect(lean?.parsed, source).toBe(true);
    if (lean === undefined || !lean.parsed) continue;
    const path = join(dir, `case${i}.mjs`);
    writeFileSync(path, ts.transpileModule(source, { compilerOptions: { target: ts.ScriptTarget.ESNext, module: ts.ModuleKind.ESNext } }).outputText);
    const mod = (await import(pathToFileURL(path).href)) as { f: (...args: Array<number | boolean>) => boolean };
    for (const [j, args] of inputs.entries()) {
      expect(lean.results[j]?.value, source).toBe(mod.f(...argumentsFor(i, args)));
    }
  }
});

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
    { source: 'export function f(): bigint | undefined { return undefined; }', args: [] },
    { source: 'export function f(a: bigint): undefined | bigint { return a; }', args: [7n] },
    {
      source: 'export function f(a: bigint): bigint { let x: bigint | undefined = undefined; x = a; return x ?? 0n; }',
      args: [9n],
    },
    { source: 'export function f(a?: bigint): bigint | undefined { const x: bigint | undefined = a; return x; }', args: [] },
    { source: 'export function f(a?: bigint): bigint | undefined { const x: bigint | undefined = a; return x; }', args: [0n] },
    ...[
      'x !== undefined && x > 0n',
      'undefined === x || x > 0n',
      '!(x === undefined) && x > 0n',
      '!(undefined !== x) || x > 0n',
      'x === undefined ? false : x > 0n',
      '!(x === undefined) ? x > 0n : false',
    ].flatMap((body) => [[], [-1n], [0n], [1n]].map((args) => ({
      source: `export function f(x?: bigint): boolean { return ${body}; }`,
      args,
    }))),
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

// `at` and `slice` read a number argument with `ToIntegerOrInfinity`: a
// fraction rounds toward zero, `NaN` is 0, and an infinite or huge number lands
// past an end of the array. Random programs rarely pass such an index, so
// these cases run each shape on each kind of number.
test('the interpreter reads the index of at and slice as Node does', async () => {
  const sources = [
    'export function f(xs: ReadonlyArray<bigint>, i: number): bigint | null { return xs.at(i) ?? null; }',
    'export function f(xs: ReadonlyArray<bigint>, i: number): ReadonlyArray<bigint> { return xs.slice(i); }',
    'export function f(xs: ReadonlyArray<bigint>, i: number): ReadonlyArray<bigint> { return xs.slice(1, i); }',
    'export function f(xs: ReadonlyArray<bigint>, i: number): ReadonlyArray<bigint> { return xs.slice(i, -1); }',
  ];
  const indexes = [0, -0, 1, -1, 0.5, -0.5, 2.7, -2.7, 3, 9, -9, NaN, Infinity, -Infinity, 2 ** 53, -(2 ** 53), 1e308, -1e308];
  const xs = [10n, 20n, 30n, 40n];
  const cases = sources.flatMap((source) => indexes.map((i) => ({ source, args: [xs, i] })));
  const input = {
    programs: cases.map(({ source, args }) => ({ source, calls: [{ function: 'f', args: args.map(encode) }] })),
  };
  const run = spawnSync(tolean, ['interpret'], { input: JSON.stringify(input), encoding: 'utf8' });
  expect(run.status, run.stderr).toBe(0);
  const results = (JSON.parse(run.stdout) as { programs: Array<Interpreted> }).programs;
  const dir = mkdtempSync(join(tmpdir(), 'tolean-index-'));
  for (const [k, source] of sources.entries()) {
    const path = join(dir, `case${k}.mjs`);
    writeFileSync(path, ts.transpileModule(source, { compilerOptions: { target: ts.ScriptTarget.ESNext, module: ts.ModuleKind.ESNext } }).outputText);
    const mod = (await import(pathToFileURL(path).href)) as { f: (...a: Array<unknown>) => unknown };
    for (const [j, i] of indexes.entries()) {
      const lean = results[k * indexes.length + j];
      expect(lean?.parsed, source).toBe(true);
      if (lean === undefined || !lean.parsed) continue;
      const value = lean.results[0]?.value;
      expect(value === undefined ? 'no value' : canonical(value), `${source} with ${i}`).toBe(canonical(encode(mod.f(xs, i))));
    }
  }
});

test('optional array indexing agrees with Node', async () => {
  const sources = [
    'export function f(xs: ReadonlyArray<bigint> | null): bigint { return xs?.[0] ?? 7n; }',
    'export function f(xs?: ReadonlyArray<bigint>): bigint { return xs?.[1] ?? 9n; }',
  ];
  const arrays = fc.sample(fc.array(fc.bigInt(), { maxLength: 8 }), { seed, numRuns: 50 });
  const args: Array<unknown> = [null, undefined, [], ...arrays];
  const input = {
    programs: sources.map(source => ({
      source,
      calls: args.map(xs => ({ function: 'f', args: [encode(xs)] })),
    })),
  };
  const run = spawnSync(tolean, ['interpret'], { input: JSON.stringify(input), encoding: 'utf8' });
  expect(run.status, run.stderr).toBe(0);
  const results = (JSON.parse(run.stdout) as { programs: Array<Interpreted> }).programs;
  const dir = mkdtempSync(join(tmpdir(), 'tolean-optional-index-'));
  for (const [i, source] of sources.entries()) {
    const path = join(dir, `case${i}.mjs`);
    writeFileSync(path, ts.transpileModule(source, {
      compilerOptions: { target: ts.ScriptTarget.ESNext, module: ts.ModuleKind.ESNext },
    }).outputText);
    const mod = (await import(pathToFileURL(path).href)) as { f: (xs: unknown) => unknown };
    const result = results[i];
    expect(result?.parsed, source).toBe(true);
    if (result === undefined || !result.parsed) continue;
    for (const [j, xs] of args.entries()) {
      const value = result.results[j]?.value;
      expect(value === undefined ? 'no value' : canonical(value), source)
        .toBe(canonical(encode(mod.f(xs))));
    }
  }
});

test('an absent optional receiver skips the index expression', async () => {
  const source = 'export function f(xs: ReadonlyArray<bigint> | null): bigint { return xs?.[missing()] ?? 11n; }';
  const run = spawnSync(tolean, ['interpret'], {
    input: JSON.stringify({ programs: [{ source, calls: [{ function: 'f', args: [null] }] }] }),
    encoding: 'utf8',
  });
  expect(run.status, run.stderr).toBe(0);
  const result = (JSON.parse(run.stdout) as { programs: Array<Interpreted> }).programs[0];
  expect(result?.parsed).toBe(true);
  if (result === undefined || !result.parsed) return;
  const dir = mkdtempSync(join(tmpdir(), 'tolean-optional-index-skip-'));
  const path = join(dir, 'skip.mjs');
  writeFileSync(path, ts.transpileModule(source, {
    compilerOptions: { target: ts.ScriptTarget.ESNext, module: ts.ModuleKind.ESNext },
  }).outputText);
  const mod = (await import(pathToFileURL(path).href)) as { f: (xs: null) => unknown };
  const value = result.results[0]?.value;
  expect(value === undefined ? 'no value' : canonical(value)).toBe(canonical(encode(mod.f(null))));
});

test('optional indexed member access handles every kind of number index', async () => {
  const source = 'export interface Item { readonly value: bigint; }\nexport function f(xs: ReadonlyArray<Item> | null, i: number): bigint { return xs?.[i]?.value ?? 17n; }';
  const arrays: Array<unknown> = [null, undefined, [], [{ value: 3n }, { value: 5n }, { value: 8n }]];
  const indexes = [NaN, Infinity, -Infinity, -0, 0, 1, 2, 3, -1, 0.5, Number.MAX_SAFE_INTEGER];
  const args = arrays.flatMap(xs => indexes.map(i => [xs, i]));
  const run = spawnSync(tolean, ['interpret'], {
    input: JSON.stringify({ programs: [{ source, calls: args.map(a => ({
      function: 'f', args: a.map(encode),
    })) }] }),
    encoding: 'utf8',
  });
  expect(run.status, run.stderr).toBe(0);
  const result = (JSON.parse(run.stdout) as { programs: Array<Interpreted> }).programs[0];
  expect(result?.parsed).toBe(true);
  if (result === undefined || !result.parsed) return;
  const dir = mkdtempSync(join(tmpdir(), 'tolean-optional-number-index-'));
  const path = join(dir, 'index.mjs');
  writeFileSync(path, ts.transpileModule(source, {
    compilerOptions: { target: ts.ScriptTarget.ESNext, module: ts.ModuleKind.ESNext },
  }).outputText);
  const mod = (await import(pathToFileURL(path).href)) as { f: (...xs: Array<unknown>) => unknown };
  for (const [j, a] of args.entries()) {
    const value = result.results[j]?.value;
    expect(value === undefined ? 'no value' : canonical(value))
      .toBe(canonical(encode(mod.f(...a))));
  }
});

test('optional tuple and Record indices agree with Node', async () => {
  const source = readFileSync(new URL('./corpus/translate/accept/optionalTupleRecordIndex.ts', import.meta.url), 'utf8');
  const calls: Array<{ function: string; args: Array<unknown> }> = [];
  const values = [undefined, 0n, -3n, ...fc.sample(fc.bigInt(), { seed, numRuns: 20 })];
  for (const value of values) {
    calls.push({ function: 'optionalValue', args: [[value, 'text']] });
    for (const key of ['apple', 'pear']) {
      calls.push({ function: 'optionalRecordValue', args: [{ apple: value, pear: 5n }, key] });
    }
  }
  for (const absent of [null, undefined]) {
    for (const name of ['first', 'last', 'literal', 'optionalValue']) {
      calls.push({ function: name, args: [absent] });
    }
    calls.push({ function: 'record', args: [absent, 'apple'] });
    calls.push({ function: 'optionalRecordValue', args: [absent, 'pear'] });
    calls.push({ function: 'shadowed', args: [true, absent] });
  }
  calls.push({ function: 'first', args: [[19n, 'value']] });
  calls.push({ function: 'last', args: [[19n, 'value']] });
  calls.push({ function: 'record', args: [{ apple: 3n, pear: 7n }, 'pear'] });
  calls.push({ function: 'literal', args: [{ apple: 3n, pear: 7n }] });
  const run = spawnSync(tolean, ['interpret'], {
    input: JSON.stringify({ programs: [{ source, calls: calls.map(c => ({
      function: c.function, args: c.args.map(encode),
    })) }] }),
    encoding: 'utf8',
  });
  expect(run.status, run.stderr).toBe(0);
  const result = (JSON.parse(run.stdout) as { programs: Array<Interpreted> }).programs[0];
  expect(result?.parsed).toBe(true);
  if (result === undefined || !result.parsed) return;
  const dir = mkdtempSync(join(tmpdir(), 'tolean-optional-tuple-record-'));
  const path = join(dir, 'index.mjs');
  writeFileSync(path, ts.transpileModule(source, {
    compilerOptions: { target: ts.ScriptTarget.ESNext, module: ts.ModuleKind.ESNext },
  }).outputText);
  const mod = (await import(pathToFileURL(path).href)) as Record<string, (...xs: Array<unknown>) => unknown>;
  for (const [i, call] of calls.entries()) {
    const fn = mod[call.function];
    if (fn === undefined) throw new Error(`missing export ${call.function}`);
    const value = result.results[i]?.value;
    expect(value === undefined ? 'no value' : canonical(value))
      .toBe(canonical(encode(fn(...call.args))));
  }
});

test('nullable conditional Record receivers agree with Node for both keys', async () => {
  const source = readFileSync(new URL('./corpus/translate/accept/nullableConditionalRecordIndex.ts', import.meta.url), 'utf8');
  const record = { a: 3n, b: 5n };
  const calls: Array<{ function: string; args: Array<unknown> }> = [];
  for (const key of ['a', 'b']) {
    calls.push({ function: 'f', args: [true, record, key] });
    calls.push({ function: 'f', args: [false, record, key] });
  }
  const run = spawnSync(tolean, ['interpret'], {
    input: JSON.stringify({ programs: [{ source, calls: calls.map(c => ({
      function: c.function, args: c.args.map(encode),
    })) }] }),
    encoding: 'utf8',
  });
  expect(run.status, run.stderr).toBe(0);
  const result = (JSON.parse(run.stdout) as { programs: Array<Interpreted> }).programs[0];
  expect(result?.parsed).toBe(true);
  if (result === undefined || !result.parsed) return;
  expect(result.accepted).toBe(true);
  const dir = mkdtempSync(join(tmpdir(), 'tolean-nullable-record-index-'));
  const path = join(dir, 'index.mjs');
  writeFileSync(path, ts.transpileModule(source, {
    compilerOptions: { target: ts.ScriptTarget.ESNext, module: ts.ModuleKind.ESNext },
  }).outputText);
  const mod = (await import(pathToFileURL(path).href)) as Record<string, (...xs: Array<unknown>) => unknown>;
  for (const [i, call] of calls.entries()) {
    const fn = mod[call.function];
    if (fn === undefined) throw new Error(`missing export ${call.function}`);
    const value = result.results[i]?.value;
    expect(value === undefined ? 'no value' : canonical(value))
      .toBe(canonical(encode(fn(...call.args))));
  }
});

// JS binds every function declaration of a block when the block starts, so a
// second declaration of `g` replaces the first for both calls, and Node gives
// 20n. The interpreter binds each where it stands, so it must give no value.
test('the interpreter gives no value for a function declared twice in a block', () => {
  const source = [
    'export function f(): bigint {',
    '  let t = 0n;',
    '  function g(): void { t += 1n; }',
    '  g();',
    '  function g(): void { t += 10n; }',
    '  g();',
    '  return t;',
    '}',
  ].join('\n');
  const input = { programs: [{ source, calls: [{ function: 'f', args: [] }] }] };
  const run = spawnSync(tolean, ['interpret'], { input: JSON.stringify(input), encoding: 'utf8' });
  expect(run.status, run.stderr).toBe(0);
  const [lean] = (JSON.parse(run.stdout) as { programs: Array<Interpreted> }).programs;
  expect(lean?.parsed).toBe(true);
  if (lean === undefined || !lean.parsed) return;
  expect(lean.results).toEqual([null]);
});

// An assignment to a `const` throws a `TypeError` in Node, so the interpreter
// must give no value for it, whatever the operator.
// A difference of keys is consistent only when every key is finite. The spec
// compares each element with itself too, and `Infinity - Infinity` is `NaN`,
// so one infinite key is enough to leave the order to the engine.
test('the interpreter sorts by a difference only when every key is finite', () => {
  const source = 'export function f(xs: ReadonlyArray<number>): number[] { return xs.toSorted((a, b) => a - b); }';
  const arrays = [[2, 1], [Infinity], [Infinity, 2], [-Infinity, 2], [NaN, 1]];
  const input = { programs: [{ source, calls: arrays.map((xs) => ({ function: 'f', args: [xs.map(encode)] })) }] };
  const run = spawnSync(tolean, ['interpret'], { input: JSON.stringify(input), encoding: 'utf8' });
  expect(run.status, run.stderr).toBe(0);
  const [lean] = (JSON.parse(run.stdout) as { programs: Array<Interpreted> }).programs;
  expect(lean?.parsed).toBe(true);
  if (lean === undefined || !lean.parsed) return;
  expect(lean.results[0]).toEqual({ value: [1, 2].map(encode) });
  expect(lean.results.slice(1)).toEqual([null, null, null, null]);
});

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

test('padding does not allocate an infinity index sentinel', () => {
  for (const method of ['padStart', 'padEnd'] as const) {
    expect(() => 'a'[method](Infinity, 'x')).toThrow(RangeError);
    const source = `export function f(n: number): string { return "a".${method}(n, "x"); }`;
    const input = { programs: [{ source, calls: [{ function: 'f', args: [encode(Infinity)] }] }] };
    const run = spawnSync(tolean, ['interpret'], { input: JSON.stringify(input), encoding: 'utf8' });
    expect(run.status, run.stderr).toBe(0);
    const [lean] = (JSON.parse(run.stdout) as { programs: Array<Interpreted> }).programs;
    expect(lean?.parsed).toBe(true);
    if (lean === undefined || !lean.parsed) continue;
    expect(lean.results).toEqual([null]);
  }
});

test('string number arguments agree with Node, including fractions and infinities', async () => {
  const bodies = [
    's.at(i) ?? null', 's.slice(i)', 's.slice(i, -1)', 's.slice(1, i)',
    's.slice(i, i + 2)', 's.startsWith("a", i)', 's.endsWith("a", i)',
    's.includes("a", i)', 's.indexOf("a", i)', 's.split("a", i)', 's.split("", i)',
  ];
  const indexes = [
    0, -0, 1, -1, 0.5, -0.5, 2.7, -2.7, NaN, Infinity, -Infinity,
    2 ** 32 - 1, 2 ** 32, 2 ** 32 + 1, -(2 ** 32) - 1,
    2 ** 53, -(2 ** 53), 1e308, -1e308,
    ...fc.sample(fc.double({ noNaN: false }), { seed, numRuns: 100 }),
  ];
  const strings = ['', 'ababa', '😀a😀', '\uD800a\uDC00'];
  const inputs = strings.flatMap((s) => indexes.map((i) => [s, i]));
  const sources = bodies.map((body) => `export function f(s: string, i: number) { return ${body}; }`);
  const run = spawnSync(tolean, ['interpret'], {
    input: JSON.stringify({ programs: sources.map((source) => ({
      source, calls: inputs.map((args) => ({ function: 'f', args: args.map(encode) })),
    })) }),
    encoding: 'utf8', maxBuffer: 16 * 1024 * 1024,
  });
  expect(run.status, run.stderr).toBe(0);
  const results = (JSON.parse(run.stdout) as { programs: Array<Interpreted> }).programs;
  for (const [k, body] of bodies.entries()) {
    const node = new Function('s', 'i', `return ${body};`) as (s: unknown, i: unknown) => unknown;
    const lean = results[k];
    expect(lean?.parsed, body).toBe(true);
    if (lean === undefined || !lean.parsed) continue;
    for (const [j, [s, i]] of inputs.entries()) {
      const value = lean.results[j]?.value;
      expect(value === undefined ? 'no value' : canonical(value), `${body} with ${String(i)}`)
        .toBe(canonical(encode(node(s, i))));
    }
  }
});

test('Date.parse accepts only deterministic format literals and agrees with Node', () => {
  const input = { programs: dateParseCases.map((s) => ({
    source: `export function f(): number { return Date.parse(${JSON.stringify(s)}); }`,
    calls: [{ function: 'f', args: [] }],
  })) };
  const run = spawnSync(tolean, ['interpret'], { input: JSON.stringify(input), encoding: 'utf8' });
  expect(run.status, run.stderr).toBe(0);
  const results = (JSON.parse(run.stdout) as { programs: Array<Interpreted> }).programs;
  for (const [i, s] of dateParseCases.entries()) {
    expect(results[i]?.accepted, s).toBe(true);
    expect(results[i]?.results[0]?.value, s).toEqual(encode(Date.parse(s)));
  }
});

test('flagless RegExp.test agrees with Node on UTF-16 strings', () => {
  const patterns = ['^(a|ab)+c$', '(?:){3,}', '^.$', 'a$', '^\\s+$', '[^a-c]*$', '(a?)*b'];
  const inputs = ['', 'a', 'abc', 'ababc', 'b', '\n', '\u2028', '😀', '\uD800', ' \t'];
  const programs = patterns.map((pattern) => ({
    source: `export function f(s: string): boolean {
      const r = /(?:${pattern})/;
      const alias = r;
      return r.test(s) && alias.test(s);
    }`,
    calls: inputs.map((s) => ({ function: 'f', args: [encode(s)] })),
  }));
  const run = spawnSync(tolean, ['interpret'], {
    input: JSON.stringify({ programs }), encoding: 'utf8',
  });
  expect(run.status, run.stderr).toBe(0);
  const results = (JSON.parse(run.stdout) as { programs: Array<Interpreted> }).programs;
  for (const [i, pattern] of patterns.entries()) {
    expect(results[i]?.accepted, pattern).toBe(true);
    for (const [j, s] of inputs.entries()) {
      expect(results[i]?.results[j]?.value, `${pattern}: ${JSON.stringify(s)}`)
        .toEqual(new RegExp(pattern).test(s));
    }
  }
});

test('Date.parse refuses local time and fallback formats', () => {
  const strings = [
    '2000-01-01T00:00', '2000-01-01T00:00:00.000', 'January 1, 2000',
    '-000000-01-01', '2000-1-1', '2000-01-01T00:00:00.00Z',
    '2000-01-01T00:00:00.0000Z', '2000-01-01T00:00Z ',
  ];
  const input = { programs: strings.map((s) => ({
    source: `export function f(): number { return Date.parse(${JSON.stringify(s)}); }`,
    calls: [{ function: 'f', args: [] }],
  })) };
  const run = spawnSync(tolean, ['interpret'], { input: JSON.stringify(input), encoding: 'utf8' });
  expect(run.status, run.stderr).toBe(0);
  const results = (JSON.parse(run.stdout) as { programs: Array<Interpreted> }).programs;
  for (const [i, s] of strings.entries()) {
    expect(results[i]?.accepted, s).toBe(false);
    expect(results[i]?.results[0], s).toBeNull();
  }
});

// `split("")` gives each code unit, so a surrogate pair becomes two lone
// surrogates. The interpreter writes each as its code units, which a JSON
// string could not hold, so Node and the interpreter agree on them.
test('the interpreter keeps the lone surrogates that split gives', async () => {
  const source = 'export function units(s: string): ReadonlyArray<string> { return s.split(""); }';
  const input = { programs: [{ source, calls: [{ function: 'units', args: [encode('😀')] }] }] };
  const run = spawnSync(tolean, ['interpret'], { input: JSON.stringify(input), encoding: 'utf8' });
  expect(run.status, run.stderr).toBe(0);
  const [lean] = (JSON.parse(run.stdout) as { programs: Array<Interpreted> }).programs;
  expect(lean?.accepted).toBe(true);
  const value = lean?.results[0]?.value;
  expect(value).toEqual([{ utf16: [0xd83d] }, { utf16: [0xde00] }]);
  expect(canonical(value as Value)).toBe(canonical(encode('😀'.split(''))));
});

// A spread of a string gives its code points: a surrogate pair stays one
// string, and a lone surrogate is a string of its own, not U+FFFD.
test('the interpreter iterates a string by code point', async () => {
  const source = 'export function chars(s: string): ReadonlyArray<string> { return [...s]; }';
  const s = 'a😀\ud800b\udc00';
  const input = { programs: [{ source, calls: [{ function: 'chars', args: [encode(s)] }] }] };
  const run = spawnSync(tolean, ['interpret'], { input: JSON.stringify(input), encoding: 'utf8' });
  expect(run.status, run.stderr).toBe(0);
  const [lean] = (JSON.parse(run.stdout) as { programs: Array<Interpreted> }).programs;
  expect(lean?.accepted).toBe(true);
  const value = lean?.results[0]?.value;
  expect(value).toEqual(['a', '😀', { utf16: [0xd800] }, 'b', { utf16: [0xdc00] }]);
  expect(canonical(value as Value)).toBe(canonical(encode([...s])));
});

// ToString of a number is abstract in the proofs, but the interpreter writes
// it, and it must write what Node writes: the fewest digits that read back as
// the same double, in the format of Number::toString.
test('the interpreter converts numbers to strings as Node does', async () => {
  const source = 'export function text(x: number): string { return "" + x; }';
  const xs = [0.1, 0.1 + 0.2, 1 / 3, -0, NaN, Infinity, -Infinity, 1e21, 1e20, 123e-20, 1e-6, 1e-7,
    5e-324, Number.MAX_VALUE, 2 ** 53, 2 ** -1022, -1.5, 4.35, 100, 9007199254740993];
  for (let i = 0; i < 200; i++) xs.push(Math.random() * 10 ** Math.floor(Math.random() * 60 - 30));
  const input = { programs: [{ source, calls: xs.map((x) => ({ function: 'text', args: [encode(x)] })) }] };
  const run = spawnSync(tolean, ['interpret'], { input: JSON.stringify(input), encoding: 'utf8' });
  expect(run.status, run.stderr).toBe(0);
  const [lean] = (JSON.parse(run.stdout) as { programs: Array<Interpreted> }).programs;
  expect(lean?.accepted).toBe(true);
  expect(lean?.results.map((r) => r.value)).toEqual(xs.map((x) => encode(String(x))));
});

// `JSON.stringify` is opaque in the proofs, but the interpreter writes its
// text, which must be the text that Node writes: an optional field that is
// missing is left out, and quotes, control characters and lone surrogates
// are escaped. The translator refuses an object here, because a caller
// chooses the order of its keys, but the interpreter runs it.
test('the interpreter writes the text of JSON.stringify', async () => {
  const source = [
    'export interface P { readonly name: string; readonly tags: ReadonlyArray<boolean>; readonly note?: string }',
    'export function render(p: P): string { return JSON.stringify(p); }',
  ].join('\n');
  const p = { name: 'a"b\\c\n\u0001\ud800😀', tags: [true, false] };
  const input = { programs: [{ source, calls: [{ function: 'render', args: [encode(p)] }] }] };
  const run = spawnSync(tolean, ['interpret'], { input: JSON.stringify(input), encoding: 'utf8' });
  expect(run.status, run.stderr).toBe(0);
  const [lean] = (JSON.parse(run.stdout) as { programs: Array<Interpreted> }).programs;
  expect(canonical(lean?.results[0]?.value as Value)).toBe(canonical(encode(JSON.stringify(p))));
});

test('interface fields describe the values at each call, not aliases between calls', async () => {
  const source = [
    'export interface P { value: bigint; extra?: bigint; }',
    'export function identity(p: P): P { return p; }',
    'export function total(ps: ReadonlyArray<P>): bigint {',
    '  let n = 0n;',
    '  for (const p of ps) { n += p.value + (p.extra ?? 0n); }',
    '  return n;',
    '}',
  ].join('\n');
  const dir = mkdtempSync(join(tmpdir(), 'tolean-interface-'));
  const path = join(dir, 'case.mjs');
  writeFileSync(path, ts.transpileModule(source, { compilerOptions: { target: ts.ScriptTarget.ESNext, module: ts.ModuleKind.ESNext } }).outputText);
  type P = { value: bigint; extra?: bigint };
  const mod = (await import(pathToFileURL(path).href)) as {
    identity: (p: P) => P;
    total: (ps: ReadonlyArray<P>) => bigint;
  };
  const p: P = { value: 1n };
  const ps = [p, p];
  const calls = [{ function: 'identity', args: [encode(p)] }, { function: 'total', args: [encode(ps)] }];
  const expected = [encode(mod.identity(p)), encode(mod.total(ps))];
  expect(mod.identity(p)).toBe(p);
  p.value = 4n;
  p.extra = 2n;
  calls.push({ function: 'total', args: [encode(ps)] });
  expected.push(encode(mod.total(ps)));
  delete p.extra;
  calls.push({ function: 'total', args: [encode(ps)] });
  expected.push(encode(mod.total(ps)));
  const input = { programs: [{ source, calls }] };
  const run = spawnSync(tolean, ['interpret'], { input: JSON.stringify(input), encoding: 'utf8' });
  expect(run.status, run.stderr).toBe(0);
  const [lean] = (JSON.parse(run.stdout) as { programs: Array<Interpreted> }).programs;
  expect(lean?.accepted).toBe(true);
  expect(lean?.results.map((r) => r.value)).toEqual(expected);
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

test('normal-completion map borrows copy the final map back without aliases', async () => {
  const change = 'function change(m: Map<bigint, bigint>, x: bigint): void { m.set(1n, x); }\n';
  const cases = [
    ...Array.from({ length: 80 }, (_, seed) => ({
      source: new Gen(seed + 1000).borrowProgram(seed % 2 === 1, seed % 3 === 0),
      refused: false,
    })),
    {
      source: change + 'export function f(x: bigint): bigint { const m = new Map<bigint, bigint>(); ' +
        'const alias = m; change(m, x); return alias.get(1n) ?? 0n; }',
      refused: true,
    },
    {
      source: change + 'export function f(x: bigint): bigint { const m = new Map<bigint, bigint>(); ' +
        'const box = { m }; change(m, x); return box.m.get(1n) ?? 0n; }',
      refused: true,
    },
    {
      source: 'function change(m: Map<bigint, bigint>, other: ReadonlyMap<bigint, bigint>): void { m.set(1n, 2n); }\n' +
        'export function f(x: bigint): bigint { const m = new Map<bigint, bigint>(); ' +
        'change(m, m); return m.get(1n) ?? 0n; }',
      refused: true,
    },
    {
      source: 'function change(a: Map<bigint, ReadonlyMap<bigint, bigint>>, b: ReadonlyMap<bigint, bigint>): void { a.set(1n, b); }\n' +
        'export function f(x: bigint): ReadonlyMap<bigint, ReadonlyMap<bigint, bigint>> { ' +
        'const a = new Map<bigint, ReadonlyMap<bigint, bigint>>(); const b = new Map<bigint, bigint>(); ' +
        'change(a, b); b.set(1n, x); return a; }',
      refused: true,
    },
    {
      source: 'function change(a: Map<bigint, ReadonlyMap<bigint, bigint>>, b: ReadonlyMap<bigint, bigint>): void { a.set(1n, b); }\n' +
        'function forward(a: Map<bigint, ReadonlyMap<bigint, bigint>>, b: ReadonlyMap<bigint, bigint>): void { change(a, b); }\n' +
        'export function f(x: bigint): ReadonlyMap<bigint, ReadonlyMap<bigint, bigint>> { ' +
        'const a = new Map<bigint, ReadonlyMap<bigint, bigint>>(); const b = new Map<bigint, bigint>(); ' +
        'forward(a, b); b.set(1n, x); return a; }',
      refused: true,
    },
    {
      source: 'function change(m: Map<bigint, bigint>, other: ReadonlyMap<bigint, bigint>): void { m.set(1n, 2n); }\n' +
        'function forward(m: Map<bigint, bigint>): void { change(m, m); }\n' +
        'export function f(x: bigint): bigint { const m = new Map<bigint, bigint>(); ' +
        'forward(m); return m.get(1n) ?? 0n; }',
      refused: true,
    },
    {
      source: 'type Other = Map<bigint, bigint>;\n' +
        'function change(a: Map<bigint, bigint>, other: ReadonlyMap<bigint, bigint>): void { a.set(1n, 5n); }\n' +
        'function forward(m: Map<bigint, bigint>, b: Other): void { change(b, m); }\n' +
        'export function f(x: bigint): boolean { const a = new Map<bigint, bigint>(); ' +
        'const b = new Map<bigint, bigint>(); forward(a, b); return b.has(1n); }',
      refused: true,
    },
    {
      source: 'function change(x: bigint, m: Map<bigint, bigint>): void { m.set(1n, x); }\n' +
        'function forward(m: Map<bigint, bigint>, x: bigint): void { change(x, m); }\n' +
        'export function f(x: bigint): bigint { const m = new Map<bigint, bigint>(); ' +
        'forward(m, x); return m.get(1n) ?? 0n; }',
    },
    {
      source: 'type Other = Map<bigint, bigint>;\n' +
        'function change(a: Map<bigint, bigint>, other: ReadonlyMap<bigint, bigint>): void { a.set(1n, 5n); }\n' +
        'function forward(m: Map<bigint, bigint>, b: Other): void { change(m, b); }\n' +
        'export function f(x: bigint): boolean { const a = new Map<bigint, bigint>(); ' +
        'const b = new Map<bigint, bigint>(); forward(a, b); return a.has(1n); }',
    },
    {
      source: 'function forward(m: Map<bigint, bigint>, x: bigint): void { change(x, m); }\n' +
        'function change(x: bigint, m: Map<bigint, bigint>): void { m.set(1n, x); }\n' +
        'export function f(x: bigint): bigint { const m = new Map<bigint, bigint>(); ' +
        'forward(m, x); return m.get(1n) ?? 0n; }',
      refused: true,
    },
    {
      source: 'function change(m: Map<bigint, bigint>): void { m.set(1n, 5n); }\n' +
        'function forward(m: Map<bigint, bigint>, change: any, x: bigint): void { change(m); }\n' +
        'export function f(n: bigint): bigint { let x = 0n; ' +
        'function g(z: Map<bigint, bigint>): void { x = 5n; } ' +
        'const m = new Map<bigint, bigint>(); forward(m, g, x); return x; }',
      refused: true,
    },
  ];
  const inputs = [-9n, 0n, 17n];
  const run = spawnSync(tolean, ['interpret'], {
    input: JSON.stringify({ programs: cases.map(({ source }) => ({
      source, calls: inputs.map(x => ({ function: 'f', args: [encode(x)] })),
    })) }),
    encoding: 'utf8',
  });
  expect(run.status, run.stderr).toBe(0);
  const results = (JSON.parse(run.stdout) as { programs: Array<Interpreted> }).programs;
  const dir = mkdtempSync(join(tmpdir(), 'tolean-map-borrows-'));
  for (const [i, { source, refused }] of cases.entries()) {
    const lean = results[i];
    expect(lean?.parsed, source).toBe(true);
    const path = join(dir, `case${i}.mjs`);
    writeFileSync(path, ts.transpileModule(source, {
      compilerOptions: { target: ts.ScriptTarget.ESNext, module: ts.ModuleKind.ESNext },
    }).outputText);
    const mod = (await import(pathToFileURL(path).href)) as { f: (x: bigint) => bigint };
    if (!lean?.parsed) continue;
    for (const [j, x] of inputs.entries()) {
      const expected = encode(mod.f(x));
      if (refused) expect(lean.results[j] ?? null, source).toBeNull();
      else expect(lean.results[j]?.value, source).toEqual(expected);
    }
  }
});

// Calls that return a value still have no state-carrying result.
test('map calls preserve the boundary between readonly inputs and pending borrows', async () => {
  const change = 'function change(m: Map<bigint, bigint>): boolean { m.set(1n, 2n); return true; }\n';
  const cases = [
    {
      source: change + 'export function f(): boolean { const m = new Map<bigint, bigint>(); ' +
        'const done = change(m); return m.has(1n); }',
      refused: true,
    },
    {
      source: change + 'export function f(): boolean { const m = new Map<bigint, bigint>(); const alias = m; ' +
        'const done = change(m); return alias.has(1n); }',
      refused: true,
    },
    {
      source: change + 'export function f(): boolean { const m = new Map<bigint, bigint>(); const box = { m }; ' +
        'const done = change(m); return box.m.has(1n); }',
      refused: true,
    },
    {
      source: 'function change(m: Map<bigint, bigint>, other: ReadonlyMap<bigint, bigint>): boolean { ' +
        'm.set(1n, 2n); return other.has(1n); }\n' +
        'export function f(): boolean { const m = new Map<bigint, bigint>(); return change(m, m); }',
      refused: true,
    },
    {
      source: 'function read(m: ReadonlyMap<bigint, bigint>): boolean { return m.has(1n); }\n' +
        'export function f(): boolean { const m = new Map<bigint, bigint>([[1n, 2n]]); return read(m); }',
      refused: false,
    },
  ];
  const input = { programs: cases.map(({ source }) => ({ source, calls: [{ function: 'f', args: [] }] })) };
  const run = spawnSync(tolean, ['interpret'], { input: JSON.stringify(input), encoding: 'utf8' });
  expect(run.status, run.stderr).toBe(0);
  const results = (JSON.parse(run.stdout) as { programs: Array<Interpreted> }).programs;
  const dir = mkdtempSync(join(tmpdir(), 'tolean-map-calls-'));
  for (const [i, { source, refused }] of cases.entries()) {
    const lean = results[i];
    expect(lean?.parsed, source).toBe(true);
    const path = join(dir, `case${i}.mjs`);
    writeFileSync(path, ts.transpileModule(source, {
      compilerOptions: { target: ts.ScriptTarget.ESNext, module: ts.ModuleKind.ESNext },
    }).outputText);
    const mod = (await import(pathToFileURL(path).href)) as { f: () => boolean };
    expect(mod.f(), source).toBe(true);
    if (lean === undefined || !lean.parsed) continue;
    if (refused) {
      expect(lean.results[0] ?? null, source).toBeNull();
    } else {
      expect(lean.results[0]?.value, source).toEqual(encode(mod.f()));
    }
  }
});

// A map or a set compares number keys with SameValueZero, not `===`: `NaN` is
// the same key as `NaN`, and `0` the same as `-0`. A new key `-0` is stored as
// `0`, which a loop over the keys shows. The random programs rarely build these
// cases, so each one is here, and the interpreter must agree with Node on it.
test('the interpreter compares number keys of a map or a set with SameValueZero', async () => {
  const fn = (ret: string, body: string) => `export function f(b: boolean): ${ret} { ${body} }`;
  const sources = [
    fn('number', 'const s = new Set<number>(); s.add(NaN); s.add(NaN); return s.size;'),
    fn('boolean', 'const s = new Set<number>([NaN]); return s.has(NaN);'),
    fn('number', 'const s = new Set<number>([0, -0]); return s.size;'),
    fn('boolean', 'const s = new Set<number>(); s.add(-0); return s.has(0);'),
    fn('number', 'const s = new Set<number>(); s.add(-0); let x = 1; for (const e of s) { x = e; } return x;'),
    fn('number', 'const s = new Set<number>([NaN, 1]); s.delete(NaN); return s.size;'),
    fn('bigint', 'const m = new Map<number, bigint>(); m.set(NaN, 1n); m.set(NaN, 2n); return m.get(NaN) ?? 0n;'),
    fn('bigint', 'const m = new Map<number, bigint>(); m.set(0, 1n); m.set(-0, 2n); return m.get(0) ?? 0n;'),
    fn('number', 'const m = new Map<number, bigint>([[-0, 1n]]); let x = 1; for (const e of m) { x = e[0]; } return x;'),
    // The entry keeps the key that it has, so a later `set(-0, v)` leaves `0`.
    fn('number', 'const m = new Map<number, bigint>(); m.set(0, 1n); m.set(-0, 2n); let x = 1; for (const e of m) { x = e[0]; } return x;'),
    fn('number', 'const m = new Map<number, bigint>([[NaN, 1n], [2, 2n]]); m.delete(NaN); return m.size;'),
  ];
  const input = { programs: sources.map((source) => ({ source, calls: [{ function: 'f', args: [true] }] })) };
  const run = spawnSync(tolean, ['interpret'], { input: JSON.stringify(input), encoding: 'utf8' });
  expect(run.status, run.stderr).toBe(0);
  const results = (JSON.parse(run.stdout) as { programs: Array<Interpreted> }).programs;
  const dir = mkdtempSync(join(tmpdir(), 'tolean-keys-'));
  for (const [i, source] of sources.entries()) {
    const lean = results[i];
    expect(lean?.accepted, source).toBe(true);
    const path = join(dir, `case${i}.mjs`);
    writeFileSync(path, ts.transpileModule(source, { compilerOptions: { target: ts.ScriptTarget.ESNext, module: ts.ModuleKind.ESNext } }).outputText);
    const mod = (await import(pathToFileURL(path).href)) as { f: (b: boolean) => unknown };
    const value = lean?.results[0]?.value;
    expect(value === undefined ? 'no value' : canonical(value), source).toBe(canonical(encode(mod.f(true))));
  }
});
