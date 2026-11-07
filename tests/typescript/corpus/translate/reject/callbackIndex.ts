// expect: 3:10 the index and array parameters are not supported yet
export function f(xs: ReadonlyArray<bigint>): ReadonlyArray<bigint> {
  return xs.map((x, i) => x);
}
