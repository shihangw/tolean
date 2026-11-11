// When the file uses `number`, each structure takes the number model `N` as a
// parameter. Lean does not infer `N` from the value of the spread, so the
// update writes its type out, as an object literal does.
export interface Item {
  readonly count: bigint;
  readonly weight: number;
}

export function heavier(it: Item, by_: number): number {
  const q = { ...it, weight: it.weight + by_ };
  return q.weight;
}

export function counted(it: Item): bigint {
  const q = { ...it, count: 1n };
  return q.count;
}

export function same(it: Item): Item {
  const q = { ...it };
  return q;
}
