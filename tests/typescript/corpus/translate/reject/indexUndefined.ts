// expect: 4:10 arithmetic needs two bigints or two numbers
// xs[0] is undefined when xs is empty, whatever noUncheckedIndexedAccess says.
export function f(xs: ReadonlyArray<bigint>): bigint {
  return xs[0] + 1n;
}
