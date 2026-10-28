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
 *   holds for every program that the parser accepts, in the subset or not.
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
  | Array<Value>
  | { object: Array<[string, Value]> };

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
  if ('bigint' in v) return BigInt(v.bigint);
  if ('number' in v) return ofBits(v.number);
  return Object.fromEntries(v.object.map(([k, x]) => [k, decode(x)]));
}

/** `v` as text, with every `NaN` written the same way. */
function canonical(v: Value): string {
  const strip = (w: Value): unknown => {
    if (w === null || typeof w === 'boolean' || typeof w === 'string') return w;
    if (Array.isArray(w)) return w.map(strip);
    if ('number' in w) return { number: Number.isNaN(ofBits(w.number)) ? 'NaN' : w.number };
    if ('bigint' in w) return w;
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
      return fc.oneof(fc.constantFrom('', 'a', 'ab', 'é', '😀'), fc.string({ unit: 'grapheme', maxLength: 4 }));
    case 'nullable':
      return fc.option(arbitrary(t.of, sig), { nil: null });
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
type Interpreted = { parsed: false } | { parsed: true; accepted: boolean; results: Array<{ value: Value } | null> };
type NodeResult = { returns: unknown } | { throws: string };

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
        actual = { throws: e instanceof Error ? e.name : String(e) };
      }
      if (expected !== null) {
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
