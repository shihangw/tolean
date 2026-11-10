// expect: 3:21 the index of an array is a number
export function f(xs: ReadonlyArray<bigint>): ReadonlyArray<bigint> {
  return xs.map((x, i: bigint) => x);
}
