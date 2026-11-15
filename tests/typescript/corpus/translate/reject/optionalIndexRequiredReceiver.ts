// expect: 3:10 optional indexing requires a nullable or optional array, tuple or Record
export function f(xs: ReadonlyArray<bigint>): bigint {
  return xs?.[0] ?? 0n;
}
