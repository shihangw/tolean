/**
 * The translators write bigint `a / b` as `Int.tdiv a b` and `a % b` as
 * `Int.tmod a b`, for a nonzero literal `b`. This checks that claim against
 * the JS engine: Node computes `a / b` and `a % b` for random pairs, and Lean
 * checks each answer with `#guard`. Run it where `lean` is on the PATH
 * (`nix develop`).
 */
import { spawnSync } from 'node:child_process';
import { mkdtempSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';

import fc from 'fast-check';
import { expect, test } from 'vitest';

const operand = fc.oneof(
  fc.bigInt({ min: -10n, max: 10n }),
  fc.bigInt({ min: -(2n ** 64n), max: 2n ** 64n }),
  fc.bigInt({ min: -(2n ** 200n), max: 2n ** 200n }),
);

test('JS bigint / and % are Lean Int.tdiv and Int.tmod', () => {
  const pairs = fc.sample(
    fc.tuple(operand, operand.filter((b) => b !== 0n)),
    { numRuns: 2000, seed: 1 },
  );
  // The signs of both operands, and |a| < |b|.
  pairs.push([7n, 2n], [-7n, 2n], [7n, -2n], [-7n, -2n], [1n, 3n], [-1n, 3n], [0n, -5n]);
  const lines = pairs.flatMap(([a, b]) => [
    `#guard Int.tdiv (${a}) (${b}) == (${a / b})`,
    `#guard Int.tmod (${a}) (${b}) == (${a % b})`,
  ]);
  const file = join(mkdtempSync(join(tmpdir(), 'tolean-division-')), 'Division.lean');
  writeFileSync(file, `${lines.join('\n')}\n`);

  const run = spawnSync('lean', [file], { encoding: 'utf8' });

  expect(run.error).toBeUndefined();
  expect(run.stdout + run.stderr).toBe('');
  expect(run.status).toBe(0);
}, 120_000);
