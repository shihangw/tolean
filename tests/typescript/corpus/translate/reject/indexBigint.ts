// expect: 3:13 the index of an array must be a number
export function f(xs: ReadonlyArray<bigint>): bigint {
  return xs[0n] ?? 0n;
}
