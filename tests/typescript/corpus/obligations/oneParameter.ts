export function f(xs: ReadonlyArray<bigint>): bigint[] {
  return xs.toSorted((a, b) => a === a ? 0 : 0);
}
