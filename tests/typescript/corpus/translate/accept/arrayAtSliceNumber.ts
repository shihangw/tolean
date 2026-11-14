// `xs.at(i)` and `xs.slice(a, b)` with a number that is not an integer
// literal read its integer as `ToIntegerOrInfinity` does: a fraction rounds
// toward zero, `NaN` is 0, and `Infinity` is past the end. The output calls
// `JSNumber.atIndex?` and `JSNumber.sliceInt` on `JSNumber.toIndexInt i`.
export function nth(xs: ReadonlyArray<bigint>, i: number): bigint {
  return xs.at(i) ?? 0n;
}

export function hasNth(xs: ReadonlyArray<string>, i: number): boolean {
  return xs.at(i) !== undefined;
}

export function fromEnd(xs: ReadonlyArray<bigint>, i: number): bigint {
  return xs.at(-i) ?? 0n;
}

export function suffix(xs: ReadonlyArray<bigint>, i: number): ReadonlyArray<bigint> {
  return xs.slice(i);
}

export function firstN(xs: ReadonlyArray<boolean>, n: number): ReadonlyArray<boolean> {
  return xs.slice(0, n);
}

export function between(xs: ReadonlyArray<bigint>, lo: number, hi: number): ReadonlyArray<bigint> {
  return xs.slice(lo, hi);
}

export function trimmed(xs: ReadonlyArray<bigint>, i: number): ReadonlyArray<bigint> {
  return xs.slice(i, -1);
}

export function prefixSum(xs: ReadonlyArray<bigint>, n: number): bigint {
  return xs.slice(0, n).reduce((sum, x) => sum + x, 0n);
}

export function laterBig(xs: ReadonlyArray<bigint>, i: number): ReadonlyArray<bigint> {
  return xs.slice(i).filter((x) => x > 0n);
}
