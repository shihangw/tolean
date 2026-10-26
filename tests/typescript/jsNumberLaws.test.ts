/**
 * `SafeIntLaws` and `SpecialValueLaws` (tolean/TypeScript/Spec/Number.lean),
 * checked against real JS doubles.
 *
 * The laws are the only facts about `number` that the proofs may use. They are
 * claims about the JS engine, so Lean cannot check them; this file checks each
 * one here. Each check records the exact Lean statement it was written for,
 * and the tests fail when a law is added, removed, renamed or restated in the
 * Lean file without the matching check changing here too.
 */
import { describe, expect, test } from 'vitest';

import { readFileSync } from 'node:fs';
import fc from 'fast-check';

const MAX = Number.MAX_SAFE_INTEGER;

/** The Lean `toSafeInt`: the integer a double is, when `Number.isSafeInteger`. */
const toSafeInt = (x: number): bigint | null =>
  Number.isSafeInteger(x) ? BigInt(x) : null;

const inRange = (i: bigint): boolean => -BigInt(MAX) <= i && i <= BigInt(MAX);

// Edges first: the range ends, ±0, and the values just past the range.
const safeInteger = fc.oneof(
  fc.constantFrom(0, -0, 1, -1, MAX, -MAX, MAX - 1, 2 ** 52, -(2 ** 52)),
  fc.integer({ min: -1000, max: 1000 }),
  fc.maxSafeInteger(),
);
const anyNumber = fc.oneof(
  safeInteger,
  fc.double(),
  fc.constantFrom(NaN, Infinity, -Infinity, 0.5, 2 ** 53, -(2 ** 53), MAX + 2),
);

const RUNS = { numRuns: 20_000 };

const exact =
  (
    operation: (a: number, b: number) => number,
    exactOperation: (i: bigint, j: bigint) => bigint,
  ) =>
  (): void =>
    fc.assert(
      fc.property(safeInteger, safeInteger, (a, b) => {
        const expected = exactOperation(BigInt(a), BigInt(b));
        if (inRange(expected)) {
          expect(toSafeInt(operation(a, b))).toBe(expected);
        }
      }),
      RUNS,
    );

const agrees =
  (
    compare: (a: number, b: number) => boolean,
    exactCompare: (i: bigint, j: bigint) => boolean,
  ) =>
  (): void =>
    fc.assert(
      fc.property(safeInteger, safeInteger, (a, b) => {
        expect(compare(a, b)).toBe(exactCompare(BigInt(a), BigInt(b)));
      }),
      RUNS,
    );

const BINARY =
  '∀ {a b : N} {i j : Int}, toSafeInt a = some i → toSafeInt b = some j →';

/**
 * One check per field of `SafeIntLaws`, under the same name. `statement` is
 * the Lean statement the check was written for, as one line. When a law
 * changes in Lean, the check must be rewritten for the new statement.
 */
const CHECKS: Record<string, { statement: string; check: () => void }> = {
  toSafeInt_inRange: {
    statement: '∀ {x : N} {i : Int}, toSafeInt x = some i → InRange i',
    check: () =>
      fc.assert(
        fc.property(anyNumber, (x) => {
          const i = toSafeInt(x);
          expect(i == null || inRange(i)).toBe(true);
        }),
        RUNS,
      ),
  },
  ofSafeInt: {
    statement:
      '∀ {i : Int}, InRange i → toSafeInt (ofSafeInt (N := N) i) = some i',
    // An integer literal in range evaluates to that integer.
    check: () =>
      fc.assert(
        fc.property(safeInteger, (a) => {
          const literal = BigInt(a).toString();
          expect(toSafeInt(Number(literal))).toBe(BigInt(literal));
        }),
        RUNS,
      ),
  },
  add: {
    statement: `${BINARY} InRange (i + j) → toSafeInt (add a b) = some (i + j)`,
    check: exact(
      (a, b) => a + b,
      (i, j) => i + j,
    ),
  },
  sub: {
    statement: `${BINARY} InRange (i - j) → toSafeInt (sub a b) = some (i - j)`,
    check: exact(
      (a, b) => a - b,
      (i, j) => i - j,
    ),
  },
  mul: {
    statement: `${BINARY} InRange (i * j) → toSafeInt (mul a b) = some (i * j)`,
    check: exact(
      (a, b) => a * b,
      (i, j) => i * j,
    ),
  },
  neg: {
    statement:
      '∀ {a : N} {i : Int}, toSafeInt a = some i → toSafeInt (neg a) = some (-i)',
    check: () =>
      fc.assert(
        fc.property(safeInteger, (a) => {
          expect(toSafeInt(-a)).toBe(-BigInt(a));
        }),
        RUNS,
      ),
  },
  lt: {
    statement: `${BINARY} lt a b = decide (i < j)`,
    check: agrees(
      (a, b) => a < b,
      (i, j) => i < j,
    ),
  },
  le: {
    statement: `${BINARY} le a b = decide (i ≤ j)`,
    check: agrees(
      (a, b) => a <= b,
      (i, j) => i <= j,
    ),
  },
  eq: {
    statement: `${BINARY} eq a b = decide (i = j)`,
    check: agrees(
      (a, b) => a === b,
      (i, j) => i === j,
    ),
  },
};

// Every kind of double: NaN in several forms, ±Infinity, ±0, subnormals,
// fractions, the largest finite value, and safe integers.
const nanValue = fc.constantFrom(
  NaN,
  0 / 0,
  Infinity - Infinity,
  Math.sqrt(-1),
  Number.NaN,
);
const anyDouble = fc.oneof(
  anyNumber,
  nanValue,
  fc.constantFrom(
    Infinity,
    -Infinity,
    0,
    -0,
    5e-324,
    -5e-324,
    0.1,
    Number.MAX_VALUE,
  ),
);

/** The law holds for every double `a`. */
const always = (holds: (a: number) => boolean) => (): void =>
  fc.assert(
    fc.property(anyDouble, (a) => {
      expect(holds(a)).toBe(true);
    }),
    RUNS,
  );

/** The law holds for every `NaN` paired with every double `b`. */
const withNaN = (holds: (nan: number, b: number) => boolean) => (): void =>
  fc.assert(
    fc.property(nanValue, anyDouble, (nan, b) => {
      expect(holds(nan, b)).toBe(true);
    }),
    RUNS,
  );

/** A law about constants: one fact, checked once. */
const fact = (holds: boolean) => (): void => {
  expect(holds).toBe(true);
};

/** One check per field of `SpecialValueLaws`, under the same name. */
const SPECIAL_VALUE_CHECKS: Record<
  string,
  { statement: string; check: () => void }
> = {
  eq_refl: {
    statement: '∀ {a : N}, isNaN a = false → eq a a = true',
    check: always((a) => Number.isNaN(a) || a === a),
  },
  eq_symm: {
    statement: '∀ {a b : N}, eq a b = eq b a',
    check: () =>
      fc.assert(
        fc.property(anyDouble, anyDouble, (a, b) => {
          expect(a === b).toBe(b === a);
        }),
        RUNS,
      ),
  },
  nan_eq: {
    statement: '∀ {a b : N}, isNaN a = true → eq a b = false',
    check: withNaN((nan, b) => nan !== b),
  },
  nan_lt: {
    statement: '∀ {a b : N}, isNaN a = true → lt a b = false ∧ lt b a = false',
    check: withNaN((nan, b) => !(nan < b) && !(b < nan)),
  },
  nan_le: {
    statement: '∀ {a b : N}, isNaN a = true → le a b = false ∧ le b a = false',
    check: withNaN((nan, b) => !(nan <= b) && !(b <= nan)),
  },
  nan_add: {
    statement:
      '∀ {a b : N}, isNaN a = true → isNaN (add a b) = true ∧ isNaN (add b a) = true',
    check: withNaN((nan, b) => Number.isNaN(nan + b) && Number.isNaN(b + nan)),
  },
  nan_sub: {
    statement:
      '∀ {a b : N}, isNaN a = true → isNaN (sub a b) = true ∧ isNaN (sub b a) = true',
    check: withNaN((nan, b) => Number.isNaN(nan - b) && Number.isNaN(b - nan)),
  },
  nan_mul: {
    statement:
      '∀ {a b : N}, isNaN a = true → isNaN (mul a b) = true ∧ isNaN (mul b a) = true',
    check: withNaN((nan, b) => Number.isNaN(nan * b) && Number.isNaN(b * nan)),
  },
  isNaN_nan: {
    statement: 'isNaN (nan (N := N)) = true',
    check: fact(Number.isNaN(NaN)),
  },
  isNaN_posInf: {
    statement: 'isNaN (posInf (N := N)) = false',
    check: fact(!Number.isNaN(Infinity)),
  },
  isNaN_negInf: {
    statement: 'isNaN (negInf (N := N)) = false',
    check: fact(!Number.isNaN(-Infinity)),
  },
  isFinite_posInf: {
    statement: 'isFinite (posInf (N := N)) = false',
    check: fact(!Number.isFinite(Infinity)),
  },
  isFinite_negInf: {
    statement: 'isFinite (negInf (N := N)) = false',
    check: fact(!Number.isFinite(-Infinity)),
  },
  isFinite_not_nan: {
    statement: '∀ {a : N}, isFinite a = true → isNaN a = false',
    check: always((a) => !Number.isFinite(a) || !Number.isNaN(a)),
  },
  safe_finite: {
    statement: '∀ {a : N} {i : Int}, toSafeInt a = some i → isFinite a = true',
    check: always((a) => toSafeInt(a) == null || Number.isFinite(a)),
  },
  lt_posInf: {
    statement: '∀ {a : N}, isFinite a = true → lt a posInf = true',
    check: always((a) => !Number.isFinite(a) || a < Infinity),
  },
  negInf_lt: {
    statement: '∀ {a : N}, isFinite a = true → lt negInf a = true',
    check: always((a) => !Number.isFinite(a) || -Infinity < a),
  },
  sub_posInf_posInf: {
    statement: 'isNaN (sub (posInf (N := N)) posInf) = true',
    check: fact(Number.isNaN(Infinity - Infinity)),
  },
};

const SOURCE = readFileSync(
  new URL('../../tolean/TypeScript/Spec/Number.lean', import.meta.url),
  'utf8',
);

/** Each field of `class <name>` in the Lean file, with its statement as one line. */
function readLaws(className: string): ReadonlyMap<string, string> {
  const lines = SOURCE.split('\n');
  const header = lines.findIndex((line) =>
    line.startsWith(`class ${className} `),
  );
  if (header === -1) {
    throw new Error(`no class ${className} in TypeScript/Spec/Number.lean`);
  }
  const laws = new Map<string, string>();
  let current: string | null = null;
  for (const line of lines.slice(header + 1)) {
    if (line.trim() !== '' && !line.startsWith('  ')) {
      break; // the class ends at the next unindented line
    }
    const start = /^ {2}(\w+) : (.*)$/.exec(line);
    if (start?.[1] != null) {
      current = start[1];
      laws.set(current, (start[2] ?? '').trim());
    } else if (current != null && /^ {4}\S/.test(line)) {
      laws.set(current, `${laws.get(current) ?? ''} ${line.trim()}`);
    } else {
      current = null;
    }
  }
  return laws;
}

describe.each([
  ['SafeIntLaws', CHECKS],
  ['SpecialValueLaws', SPECIAL_VALUE_CHECKS],
])('%s hold for JS doubles', (className, checks) => {
  const laws = readLaws(className);

  test('every law in the Lean class has a check here', () => {
    expect([...laws.keys()].sort()).toEqual(Object.keys(checks).sort());
  });

  test.each([...laws])('%s', (name, statement) => {
    const law = checks[name];
    // A restated law needs a check written for the new statement.
    expect(statement).toBe(law?.statement);
    law?.check();
  });
});
