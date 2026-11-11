// expect: 3:10 the array method 'indexOf' is not supported here
export function f(xs: ReadonlyArray<bigint>): boolean {
  return xs.indexOf(1n) === 0;
}
