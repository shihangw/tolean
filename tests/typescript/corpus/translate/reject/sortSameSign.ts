// expect: 4:32 a comparator here must compare keys
// Both tests give -1, so each of two different elements comes first.
export function f(xs: ReadonlyArray<bigint>): bigint[] {
  return xs.toSorted((a, b) => (a < b) ? -1 : (a > b) ? -1 : 0);
}
