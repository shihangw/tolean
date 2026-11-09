// expect: 3:3 set and delete are allowed only on an owned map
export function f(m: Map<string, bigint>): bigint {
  m.set('a', 1n);
  return 0n;
}
