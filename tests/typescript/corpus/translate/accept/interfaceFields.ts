export interface Leaf {
  value: bigint;
  extra?: bigint;
}

export interface Branch {
  leaf: Leaf;
  children: ReadonlyArray<Leaf>;
}

export function total(b: Branch): bigint {
  let n = b.leaf.value + (b.leaf.extra ?? 0n);
  for (const child of b.children) {
    n += child.value + (child.extra ?? 0n);
  }
  return n;
}

export function make(value: bigint): Leaf {
  return { value };
}

export function withExtra(value: bigint, extra: bigint): Leaf {
  return { value, extra };
}

export function identity(p: Leaf): Leaf {
  return p;
}
