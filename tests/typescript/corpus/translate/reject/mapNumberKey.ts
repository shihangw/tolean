// expect: 2:22 a map key must be a bigint, a string, a boolean or a literal union of strings
export function f(m: ReadonlyMap<number, bigint>): boolean {
  return m.has(1);
}
