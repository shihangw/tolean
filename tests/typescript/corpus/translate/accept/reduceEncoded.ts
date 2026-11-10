// The certificate of reduce works when the accumulator is not a primitive
// value: an array, an interface, a tuple, a literal union or a nullable
// value.
export interface Total {
  readonly count: bigint;
  readonly sum: bigint;
}

export type Sign = 'neg' | 'zero' | 'pos';

export function shifted(xs: ReadonlyArray<bigint>, init: ReadonlyArray<bigint>): ReadonlyArray<bigint> {
  return xs.reduce((a, x) => a.map(y => y + x), init);
}

export function same(xs: ReadonlyArray<bigint>, init: ReadonlyArray<bigint>): ReadonlyArray<bigint> {
  return xs.reduce((a, x) => a, init);
}

export function total(xs: ReadonlyArray<bigint>, init: Total): Total {
  return xs.reduce((t, x) => ({ count: t.count + 1n, sum: t.sum + x }), init);
}

export function minMax(xs: ReadonlyArray<bigint>, init: readonly [bigint, bigint]): readonly [bigint, bigint] {
  return xs.reduce((m, x) => [(m[0] < x) ? m[0] : x, (m[1] > x) ? m[1] : x] as const, init);
}

export function lastSign(xs: ReadonlyArray<bigint>, init: Sign): Sign {
  return xs.reduce((s: Sign, x) => ((x < 0n) ? 'neg' : (x > 0n) ? 'pos' : s), init);
}

export function firstBig(xs: ReadonlyArray<bigint>, init: bigint | null): bigint | null {
  return xs.reduce((b: bigint | null, x) => ((b === null && x > 10n) ? x : b), init);
}
