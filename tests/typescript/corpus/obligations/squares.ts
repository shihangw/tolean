export function f(xs: ReadonlyArray<bigint>): bigint[] {
  return xs.toSorted((a, b) => a * a < b * b ? -1 : a * a > b * b ? 1 : 0);
}
