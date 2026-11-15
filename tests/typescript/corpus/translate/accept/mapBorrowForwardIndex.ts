function change(x: bigint, m: Map<bigint, bigint>): void {
  m.set(1n, x);
}

function forward(m: Map<bigint, bigint>, x: bigint): void {
  change(x, m);
  return;
}

function relay(x: bigint, m: Map<bigint, bigint>): void {
  forward(m, x);
}

export function f(x: bigint): bigint {
  const m = new Map<bigint, bigint>();
  relay(x, m);
  return m.get(1n) ?? 0n;
}
