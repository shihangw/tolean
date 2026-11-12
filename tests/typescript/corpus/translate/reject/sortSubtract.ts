// expect: 3:32 a comparator here must compare keys
export function f(xs: ReadonlyArray<number>): number[] {
  return xs.toSorted((a, b) => a - b);
}
