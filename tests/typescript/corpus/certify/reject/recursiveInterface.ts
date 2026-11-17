// expect: the recursive interface Node has no certificate yet
interface Node {
  readonly value: bigint;
  readonly next: Node | null;
}

export function identity(node: Node): Node {
  return node;
}
