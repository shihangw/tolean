// expect: 3:51 a set element must be a number, a bigint, a string, a boolean or a literal union of strings
// Each value of xs.entries() is a tuple [i, x], which a set cannot hold.
export function asSet(xs: ReadonlyArray<bigint>): Set<[number, bigint]> {
  return new Set(xs.entries());
}
