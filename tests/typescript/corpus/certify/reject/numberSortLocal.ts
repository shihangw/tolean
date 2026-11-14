// expect: the sorted list must be a parameter returned directly
export function f(xs: ReadonlyArray<number>): number[] {
  const ys = xs;
  return ys.toSorted((a, b) => a - b);
}
