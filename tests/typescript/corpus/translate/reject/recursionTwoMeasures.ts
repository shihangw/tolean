// expect: 6:1 a function may call itself only on a part of one of its parameters, the same one in every call
interface Node {
  readonly next: Node | null;
}

export function both(a: Node, b: Node): bigint {
  const x = a.next;
  if (x === null) return 0n;
  const y = b.next;
  if (y === null) return 0n;
  return both(x, b) + both(a, y);
}
