// expect: 6:24 a NaN or infinite comparator cannot satisfy the required consistency obligation
// Reduced from interpreter seed 326945742.
export function f(): bigint {
  const xs: Array<bigint> = [];
  xs.push(31n);
  return xs.at(-2) ?? ([...xs].sort((a, b) => (NaN))[1] ?? 1000n);
}
