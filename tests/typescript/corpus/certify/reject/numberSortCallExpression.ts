// expect: a call with number-sort preconditions must be returned directly
function sorted(xs: ReadonlyArray<number>): number[] {
  return xs.toSorted((a, b) => a - b);
}
export function f(xs: ReadonlyArray<number>): number[] {
  return sorted(xs).map(x => x + 1);
}
