// expect: 2:53 unsupported type
function change(m: Map<bigint, bigint>, x: bigint): void {
  if (x === 0n) return;
  m.set(1n, x);
}

export function f(x: bigint): bigint {
  const m = new Map<bigint, bigint>();
  change(m, x);
  return m.get(1n) ?? 0n;
}
