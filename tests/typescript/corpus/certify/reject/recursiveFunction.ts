// expect: the recursive function sum has no certificate yet
interface Node {
  readonly value: bigint;
  readonly next: Node | null;
}

export function sum(node: Node | null): bigint {
  if (node === null) return 0n;
  return node.value + sum(node.next);
}
