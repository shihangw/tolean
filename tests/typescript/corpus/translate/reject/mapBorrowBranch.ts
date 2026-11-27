// expect: 2:63 unsupported type
function put(m: Map<string, bigint>, k: string, on: boolean): void {
  if (on) {
    m.set(k, 1n);
  }
}
export function f(k: string): bigint {
  const m = new Map<string, bigint>();
  put(m, k, true);
  return m.get(k) ?? 0n;
}
