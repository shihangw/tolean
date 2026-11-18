// expect: 4:12 a NaN or infinite comparator cannot satisfy the required consistency obligation
// Reduced from interpreter seed 326945034.
export function f(xs: ReadonlyArray<bigint>): bigint {
  return ~([...xs].sort((a, b) => (NaN))[1] ?? 1n);
}
