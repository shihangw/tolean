interface Entry {
  readonly key: string;
  readonly pair: readonly [bigint, boolean];
}

export function swap(p: readonly [bigint, string]): readonly [string, bigint] {
  return [p[1], p[0]];
}

export function sumPairs(ps: ReadonlyArray<readonly [bigint, bigint]>): bigint {
  let total = 0n;
  for (const p of ps) {
    total += p[0] + p[1];
  }
  return total;
}

export function entryKey(e: Entry): string {
  return e.pair[1] ? e.key : '';
}

export function triple(a: bigint): [bigint, bigint, bigint] {
  return [a, a + 1n, a + 2n];
}

export function third(t: [bigint, bigint, bigint]): bigint {
  return t[2];
}

export function nested(t: [bigint, [bigint, boolean]]): boolean {
  return t[1][1];
}

export function firstOrSecond(p: [bigint, bigint | null]): bigint {
  const second = p[1];
  if (second === null) return p[0];
  return second;
}
