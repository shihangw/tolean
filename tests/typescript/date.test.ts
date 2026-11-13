/**
 * The model of a `Date` (`tolean/TypeScript/Spec/Date.lean`) against the JS
 * engine. The interpreter runs `new Date(t)` with each UTC getter, and
 * `Date.UTC`, on random arguments, and Node runs the same calls. Every result
 * must have the same 64 bits, so `NaN` and `-0` count. The interpreter is
 * `.lake/build/bin/tolean`, or `$TOLEAN`.
 *
 * One kind of argument is left out on purpose. ECMA-262 lets MakeDay call a
 * year "out of range", and V8 gives `NaN` for a year past ±1,000,000, even
 * when a date argument such as `-7.3e8` brings the result back into the range
 * of a time value. The model follows the spec's arithmetic there, as
 * SpiderMonkey does.
 */
import { spawnSync } from 'node:child_process';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';

import fc from 'fast-check';
import { expect, test } from 'vitest';

const root = fileURLToPath(new URL('../../', import.meta.url));
const tolean = process.env.TOLEAN ?? join(root, '.lake/build/bin/tolean');

const bitsOf = (x: number): string => {
  const view = new DataView(new ArrayBuffer(8));
  view.setFloat64(0, x);
  return view.getBigUint64(0).toString();
};

const getters = ['getTime', 'valueOf', 'getUTCFullYear', 'getUTCMonth', 'getUTCDate', 'getUTCDay', 'getUTCHours',
  'getUTCMinutes', 'getUTCSeconds', 'getUTCMilliseconds'] as const;

const source = [
  ...getters.map((g) => `export function ${g}Of(t: number): number { return new Date(t).${g}(); }`),
  'export function utc2(y: number, m: number): number { return Date.UTC(y, m); }',
  'export function utc7(y: number, m: number, d: number, h: number, mi: number, s: number, ms: number): number {',
  '  return Date.UTC(y, m, d, h, mi, s, ms);',
  '}',
].join('\n');

type Call = { function: string; args: Array<number>; expected: number };

function run(calls: Array<Call>): Array<string> {
  const input = {
    programs: [{ source, calls: calls.map((c) => ({ function: c.function, args: c.args.map((a) => ({ number: bitsOf(a) })) })) }],
  };
  const out = spawnSync(tolean, ['interpret'], { input: JSON.stringify(input), encoding: 'utf8', maxBuffer: 1 << 28 });
  expect(out.status, out.stderr).toBe(0);
  const results = (JSON.parse(out.stdout) as { programs: Array<{ results: Array<{ value: { number: string } } | null> }> })
    .programs[0]?.results ?? [];
  return calls.flatMap((c, i) => {
    const got = results[i]?.value.number;
    return got === bitsOf(c.expected) ? [] : [`${c.function}(${c.args.join(', ')}): interpreter ${got}, Node ${bitsOf(c.expected)}`];
  });
}

// The whole range of time values, its ends and past them, and fractions.
const time = fc.oneof(
  fc.integer({ min: -8.64e15, max: 8.64e15 }),
  fc.integer({ min: -1e13, max: 1e13 }),
  fc.double({ min: -9e15, max: 9e15 }),
  fc.constantFrom(0, -0, -1, 8.64e15, -8.64e15, 8.64e15 + 1, NaN, Infinity, 0.5, -0.5, 951782400000, -62198755200001),
);
// Years and months with their edges, and the rest of the parts.
const year = fc.oneof(fc.integer({ min: -300000, max: 300000 }), fc.integer({ min: 0, max: 99 }),
  fc.constantFrom(275760, -271821, 1970, 2000, 1900, NaN, Infinity, 99.5, -0.5));
const part = fc.oneof(fc.integer({ min: -100, max: 100 }), fc.integer({ min: -1e9, max: 1e9 }), fc.double({ min: -1e6, max: 1e6 }),
  fc.constantFrom(0, -0, NaN, -Infinity, 1e300));

test('new Date(t) and its UTC getters agree with Node', () => {
  const ts = fc.sample(time, { numRuns: 3000, seed: 1 });
  const calls = ts.flatMap((t) => getters.map((g) => ({ function: `${g}Of`, args: [t], expected: new Date(t)[g]() })));
  expect(run(calls)).toEqual([]);
}, 120_000);

test('Date.UTC agrees with Node', () => {
  const two = fc.sample(fc.tuple(year, part), { numRuns: 3000, seed: 2 });
  const seven = fc.sample(fc.tuple(year, part, part, part, part, part, part), { numRuns: 3000, seed: 3 });
  const calls = [
    ...two.map(([y, m]) => ({ function: 'utc2', args: [y, m], expected: Date.UTC(y, m) })),
    ...seven.map((a) => ({ function: 'utc7', args: a, expected: Date.UTC(...a) })),
  ];
  expect(run(calls)).toEqual([]);
}, 120_000);
