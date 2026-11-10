// expect: 3:32 the callback of 'reduce' must give a value of the type of the initial value
export function f(xs: ReadonlyArray<bigint>): boolean {
  return xs.reduce((acc, x) => acc > x, 0n);
}
