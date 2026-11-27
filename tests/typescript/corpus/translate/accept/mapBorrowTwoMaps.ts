function move(a: Map<string, bigint>, b: Map<string, bigint>, k: string): void {
  a.delete(k);
  b.set(k, 1n);
}

function forward(x: Map<string, bigint>, k: string, y: Map<string, bigint>): void {
  move(y, x, k);
  x.set('seen', 2n);
}

export function f(k: string): bigint {
  const a = new Map<string, bigint>([[k, 5n]]);
  const b = new Map<string, bigint>();
  move(a, b, k);
  forward(a, k, b);
  return (a.get(k) ?? 0n) + (b.get(k) ?? 0n) + (a.get('seen') ?? 0n);
}
