// expect: 8:3 a map borrow may not pass one map for two changed parameters
function move(a: Map<string, bigint>, b: Map<string, bigint>, k: string): void {
  a.delete(k);
  b.set(k, 1n);
}
export function f(k: string): bigint {
  const a = new Map<string, bigint>();
  move(a, a, k);
  return a.get(k) ?? 0n;
}
