// expect: 3:25 the callback must give a boolean
export function f(xs: ReadonlyArray<bigint>): ReadonlyArray<bigint> {
  return xs.filter(x => x);
}
