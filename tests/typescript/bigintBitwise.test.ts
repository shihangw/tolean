/**
 * The translators write the bitwise operators on bigints with the functions
 * of `JSBigInt` (`tolean/TypeScript/Spec/BigInt.lean`), and `a ** k` as
 * `a ^ k`. This checks that claim against the JS engine: Node computes each
 * operation on random operands, and Lean checks each answer with `#guard`.
 * Run it in `nix develop` after `lake build`, so that `lake env lean` finds
 * the model.
 */
import { spawnSync } from 'node:child_process';
import { mkdtempSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';

import fc from 'fast-check';
import { expect, test } from 'vitest';

const root = fileURLToPath(new URL('../../', import.meta.url));

const operand = fc.oneof(
  fc.bigInt({ min: -10n, max: 10n }),
  fc.bigInt({ min: -(2n ** 64n), max: 2n ** 64n }),
  fc.bigInt({ min: -(2n ** 200n), max: 2n ** 200n }),
);
// A shift count, which may be negative: `a << -n` is `a >> n`.
const shift = fc.oneof(fc.bigInt({ min: -10n, max: 10n }), fc.bigInt({ min: -300n, max: 300n }));

test('JS bigint &, |, ^, ~, <<, >> and ** are the operations of JSBigInt', () => {
  const pairs = fc.sample(fc.tuple(operand, operand, shift, fc.bigInt({ min: 0n, max: 20n })), {
    numRuns: 1000,
    seed: 1,
  });
  // Each pair of signs, zero, and shifts past every bit.
  pairs.push([0n, -1n, 0n, 0n], [-1n, -1n, 1n, 1n], [5n, -3n, -1n, 2n], [-5n, 3n, 64n, 3n],
    [-(2n ** 70n), 2n ** 70n - 1n, -70n, 5n], [-1n, 0n, -1000n, 0n]);
  const lines = pairs.flatMap(([a, b, n, k]) => [
    `#guard JSBigInt.bitAnd (${a}) (${b}) == (${a & b})`,
    `#guard JSBigInt.bitOr (${a}) (${b}) == (${a | b})`,
    `#guard JSBigInt.bitXor (${a}) (${b}) == (${a ^ b})`,
    `#guard JSBigInt.bitNot (${a}) == (${~a})`,
    `#guard JSBigInt.shiftLeft (${a}) (${n}) == (${a << n})`,
    `#guard JSBigInt.shiftRight (${a}) (${n}) == (${a >> n})`,
    `#guard (((${b}) : Int) ^ (${k} : Nat)) == (${b ** k})`,
  ]);
  const file = join(mkdtempSync(join(tmpdir(), 'tolean-bitwise-')), 'Bitwise.lean');
  writeFileSync(file, `import tolean.TypeScript.Spec.BigInt\nopen tolean.TypeScript\n${lines.join('\n')}\n`);

  const run = spawnSync('lake', ['env', 'lean', file], { cwd: root, encoding: 'utf8' });

  expect(run.error).toBeUndefined();
  expect(run.stdout + run.stderr).toBe('');
  expect(run.status).toBe(0);
}, 300_000);
