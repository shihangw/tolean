// expect: 3:21 'i' shadows a name already in scope
export function f(xs: ReadonlyArray<bigint>, i: bigint): ReadonlyArray<bigint> {
  return xs.map((x, i) => x + i);
}
