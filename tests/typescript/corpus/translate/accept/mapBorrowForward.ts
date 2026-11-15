function change(m: Map<bigint, bigint>, x: bigint): void {
  m.set(1n, x);
}

function forward(m: Map<bigint, bigint>, x: bigint): void {
  change(m, x);
  m.delete(2n);
  return;
}

export function f(x: bigint): bigint {
  const m = new Map<bigint, bigint>([[2n, 9n]]);
  forward(m, x);
  return (m.get(1n) ?? 0n) + (m.get(2n) ?? 0n);
}
