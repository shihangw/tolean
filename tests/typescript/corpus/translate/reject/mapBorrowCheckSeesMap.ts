// expect: 10:9 an owned map or set may be read only
// A call that may throw out of a map borrow may not see the borrowed map.
function check(m: ReadonlyMap<bigint, bigint>): bigint {
  if (m.has(1n)) {
    throw new Error("full");
  }
  return 0n;
}
function put(m: Map<bigint, bigint>, x: bigint): void {
  check(m);
  m.set(1n, x);
}
export function f(x: bigint): bigint {
  const m = new Map<bigint, bigint>();
  put(m, x);
  return m.get(1n) ?? 0n;
}
