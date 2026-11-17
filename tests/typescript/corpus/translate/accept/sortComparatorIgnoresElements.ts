// A project must prove consistency for a captured comparator.
export function f(xs: ReadonlyArray<bigint>, key: number): bigint {
  return xs.toSorted((a, b) => key)[0] ?? 0n;
}
