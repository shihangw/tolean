// certify: required
export function f(xs: ReadonlyArray<bigint>): ReadonlyArray<bigint> {
  function same(ys: ReadonlyArray<bigint>): ReadonlyArray<bigint> {
    return ys.toSorted((a, b) => 0);
  }
  const first = same(xs);
  return same(first);
}
