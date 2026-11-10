// expect: 3:10 no callback may take the array yet
export function f(xs: ReadonlyArray<bigint>): ReadonlyArray<bigint> {
  return xs.map((x, i, all) => x);
}
