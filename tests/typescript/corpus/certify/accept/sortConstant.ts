// certify: required
export function f(xs: ReadonlyArray<bigint>): bigint[] {
  return xs.toSorted((a, b) => 0);
}
