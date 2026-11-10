// expect: 2:22 a set element must be a bigint, a string, a boolean or a literal union of strings
export function f(s: ReadonlySet<number>): boolean {
  return s.has(1);
}
