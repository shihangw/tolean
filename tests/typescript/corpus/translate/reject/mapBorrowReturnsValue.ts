// expect: 3:3 set, add and delete are allowed only on an owned map or set
function bump(m: Map<string, bigint>, k: string): bigint {
  m.set(k, 1n);
  return 1n;
}
export function f(k: string): bigint {
  const m = new Map<string, bigint>();
  const n = bump(m, k);
  return n + (m.get(k) ?? 0n);
}
