// expect: a call with number-sort preconditions inside a callback or unsupported scope
function sorted(xs: ReadonlyArray<number>): number[] {
  return xs.toSorted((a, b) => a - b);
}
export function f(xs: ReadonlyArray<ReadonlyArray<number>>): number[][] {
  return xs.map(row => sorted(row));
}
