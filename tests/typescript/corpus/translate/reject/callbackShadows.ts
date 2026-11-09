// expect: 3:17 'xs' shadows a name already in scope
export function f(xs: ReadonlyArray<bigint>): ReadonlyArray<bigint> {
  return xs.map(xs => xs);
}
