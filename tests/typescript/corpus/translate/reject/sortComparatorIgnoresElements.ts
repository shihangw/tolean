// expect: 4:10 a comparator proof obligation must read both elements
// Reduced from interpreter seed 816298054.
export function f(xs: ReadonlyArray<bigint>, key: number): bigint {
  return xs.toSorted((a, b) => key)[0] ?? 0n;
}
