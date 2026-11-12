/** Counts each score. A map compares number keys with SameValueZero, so every
 * `NaN` counts toward one key, and `0` and `-0` toward another. */
export function counts(scores: ReadonlyArray<number>): Map<number, bigint> {
  const m = new Map<number, bigint>();
  for (const x of scores) {
    m.set(x, (m.get(x) ?? 0n) + 1n);
  }
  return m;
}

export function label(names: ReadonlyMap<number, string>, k: number): string {
  return names.has(k) ? (names.get(k) ?? '') : 'none';
}

export function lastKey(m: ReadonlyMap<number, bigint>): number {
  let k = -1;
  for (const e of m) {
    k = e[0];
  }
  return k;
}
