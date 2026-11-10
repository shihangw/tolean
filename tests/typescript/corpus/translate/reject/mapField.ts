// expect: 3:10 a map has no fields here
export function f(m: ReadonlyMap<string, bigint>): bigint {
  return m.length;
}
