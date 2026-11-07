// expect: 3:10 an index may read only an element of a tuple
export function f(xs: ReadonlyArray<bigint>): bigint {
  return xs[0];
}
