// expect: 3:10 the arguments of 'slice' must be integer literals
export function f(xs: ReadonlyArray<bigint>, i: number): ReadonlyArray<bigint> {
  return xs.slice(i);
}
