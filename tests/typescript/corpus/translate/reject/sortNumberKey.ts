// expect: 4:32 a key of a comparator must be a bigint or a string
// A number key can be NaN, which makes the comparator inconsistent.
export function f(xs: ReadonlyArray<number>): number[] {
  return xs.toSorted((a, b) => (a < b) ? -1 : (a > b) ? 1 : 0);
}
