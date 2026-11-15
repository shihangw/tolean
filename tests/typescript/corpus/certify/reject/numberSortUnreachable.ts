// expect: the sorted list must be reachable from parameters through list bindings
export function f(): number[] {
  const ys = [1, 0];
  return ys.toSorted((a, b) => a - b);
}
