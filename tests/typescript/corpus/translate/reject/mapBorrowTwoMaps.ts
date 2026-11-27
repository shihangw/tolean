// expect: 2:75 unsupported type
function move(a: Map<string, bigint>, b: Map<string, bigint>, k: string): void {
  a.delete(k);
  b.set(k, 1n);
}
export function f(k: string): bigint {
  const a = new Map<string, bigint>();
  const b = new Map<string, bigint>();
  move(a, b, k);
  return b.get(k) ?? 0n;
}
