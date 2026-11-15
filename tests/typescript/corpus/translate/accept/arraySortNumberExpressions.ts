// certify: required
function sorted(xs: ReadonlyArray<number>): number[] {
  return xs.toSorted((a, b) => a - b);
}
export function mapped(xs: ReadonlyArray<number>): number[] {
  return sorted(xs).map(x => x + 1);
}
export function chosen(xs: ReadonlyArray<number>, ys: ReadonlyArray<number>, flag: boolean): number[] {
  return flag ? sorted(xs) : sorted(ys);
}
export function bound(xs: ReadonlyArray<number>): number[] {
  const ys = sorted(xs);
  return ys.map(x => x + 1);
}
