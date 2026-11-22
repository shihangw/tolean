// certify: required
export function once(xs: ReadonlyArray<bigint>): bigint[] {
  return xs.toSorted((a, b) => (0));
}
export function nested(xs: ReadonlyArray<bigint>): bigint[] {
  return xs.toSorted((a, b) => ((0)));
}
