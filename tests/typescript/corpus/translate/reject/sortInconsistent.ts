// expect: 4:32 a comparator here must compare keys
// The comparator never gives 0, so it calls an element greater than itself.
export function f(xs: ReadonlyArray<bigint>): bigint[] {
  return xs.toSorted((a, b) => (a < b) ? -1 : 1);
}
