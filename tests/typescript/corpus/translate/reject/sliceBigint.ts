// expect: 3:22 an argument of 'slice' must be a number
export function f(xs: ReadonlyArray<bigint>, i: bigint): ReadonlyArray<bigint> {
  return xs.slice(0, i);
}
