// expect: a sort precondition needs arguments reachable from parameters
function sorted(xs: ReadonlyArray<number>): number[] {
  return xs.toSorted((a, b) => a - b);
}
export function f(xs: ReadonlyArray<number>): number[] {
  return sorted([...xs, 0]);
}
