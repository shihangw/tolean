// expect: 4:10 a constant nonzero comparator is inconsistent: comparing an element with itself must give zero
// Reduced from interpreter seed 34575042.
export function f(xs: ReadonlyArray<bigint>): bigint {
  return [...xs].sort((a, b) => Math.max(1e3))[0] ?? 1n;
}
