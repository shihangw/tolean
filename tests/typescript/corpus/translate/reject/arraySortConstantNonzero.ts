// expect: 4:10 a constant nonzero comparator is inconsistent
// Reduced from interpreter seed 359337175.
export function f(xs: ReadonlyArray<bigint>): bigint[] {
  return xs.toSorted((a, b) => (0x10));
}
