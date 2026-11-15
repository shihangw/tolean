// expect: a sort precondition can only be passed from a list parameter
function sorted(xs: ReadonlyArray<number>): number[] {
  return xs.toSorted((a, b) => a - b);
}
export function f(xs: ReadonlyArray<number>): number[] {
  return sorted([...xs, 0]);
}
