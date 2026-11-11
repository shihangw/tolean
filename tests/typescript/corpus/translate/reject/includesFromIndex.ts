// expect: 4:10 'includes' takes one argument here
// The second argument, the index to start at, is not supported.
export function f(xs: ReadonlyArray<bigint>): boolean {
  return xs.includes(1n, 2);
}
