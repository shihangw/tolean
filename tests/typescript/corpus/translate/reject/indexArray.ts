// expect: 3:10 only a tuple, or a value of a Record type
export function f(xs: ReadonlyArray<bigint>): bigint {
  return xs[0];
}
