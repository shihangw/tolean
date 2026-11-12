// expect: 3:10 'toSorted' takes a comparator here
export function f(xs: ReadonlyArray<bigint>): bigint[] {
  return xs.toSorted();
}
