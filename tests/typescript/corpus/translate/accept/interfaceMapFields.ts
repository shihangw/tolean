export interface Item {
  value: bigint;
}

export function fromMap(m: ReadonlyMap<string, Item>): bigint {
  return m.get("item")?.value ?? 0n;
}

export function store(p: Item): ReadonlyMap<string, Item> {
  const m = new Map<string, Item>();
  m.set("item", p);
  return m;
}
