// expect: 4:3 the field 'Node' before this one would hide the type Node in Lean; rename the field
interface Node {
  readonly Node: bigint;
  readonly next: Node | null;
}

export function leaf(): Node {
  return { Node: 0n, next: null };
}
