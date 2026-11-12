// expect: 4:32 a comparator must give a number
// A difference of bigints is a bigint, which the sort cannot read as a number.
export function f(xs: ReadonlyArray<bigint>): bigint[] {
  return xs.toSorted((a, b) => a - b);
}
