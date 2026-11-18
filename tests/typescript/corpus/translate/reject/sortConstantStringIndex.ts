// expect: 4:10 a constant nonzero comparator is inconsistent: comparing an element with itself must give zero
// Reduced from interpreter seed 45069651.
export function f(xs: ReadonlyArray<bigint>): bigint {
  return xs.toSorted((a, b) => 'a'.indexOf('b'))[0] ?? 0n;
}
