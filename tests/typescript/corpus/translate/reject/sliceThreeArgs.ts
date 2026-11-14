// expect: 3:10 'slice' takes at most two arguments
export function f(xs: ReadonlyArray<bigint>, i: number): ReadonlyArray<bigint> {
  return xs.slice(i, 2, 3);
}
