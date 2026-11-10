export interface Tree {
  readonly value: bigint;
  readonly children: ReadonlyArray<Tree>;
}

export function total(t: Tree): bigint {
  return t.children.reduce((acc, c) => acc + total(c), t.value);
}
