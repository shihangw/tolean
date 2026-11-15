// certify: required
export function aliased(xs: ReadonlyArray<number>): number[] {
  const ys = xs;
  return ys.toSorted((a, b) => a - b);
}
export function chained(xs: ReadonlyArray<number>, ys: ReadonlyArray<number>): number[] {
  const first = xs;
  const both = [...first, ...ys];
  return both.toSorted((a, b) => (a < b) ? -1 : (a > b) ? 1 : 0);
}
export function forwarded(xs: ReadonlyArray<number>, ys: ReadonlyArray<number>): number[] {
  return chained(xs, ys);
}
export function withLiterals(xs: ReadonlyArray<number>): number[] {
  const both = [...xs, 0, 1];
  return both.toSorted((a, b) => a - b);
}
export function withLiteralArgument(xs: ReadonlyArray<number>): number[] {
  return aliased([...xs, 0, 1]);
}
