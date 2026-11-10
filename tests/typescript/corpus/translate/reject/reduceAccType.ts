// expect: 3:21 the first parameter of 'reduce' must have the type of the initial value
export function f(xs: ReadonlyArray<bigint>): bigint {
  return xs.reduce((acc: number, x) => acc + x, 0n);
}
