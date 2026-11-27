// expect: 2:69 unsupported type
function putAll(m: Map<string, bigint>, ks: ReadonlyArray<string>): void {
  for (const k of ks) {
    m.set(k, 1n);
  }
}
export function f(ks: ReadonlyArray<string>): bigint {
  const m = new Map<string, bigint>();
  putAll(m, ks);
  return BigInt(m.size);
}
