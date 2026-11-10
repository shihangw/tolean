// expect: 3:10 Only the callback of map may also take the index
export function f(xs: ReadonlyArray<bigint>): ReadonlyArray<bigint> {
  return xs.filter((x, i) => x > 0n);
}
