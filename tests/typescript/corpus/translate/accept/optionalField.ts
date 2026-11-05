export interface Item {
  readonly name: string;
  readonly price: bigint;
  readonly discount?: bigint;
  readonly note?: string;
}

// An object literal may leave an optional field out.
export function make(name: string, price: bigint): Item {
  return { name, price };
}

export function sale(name: string, price: bigint, discount: bigint): Item {
  return { name, price, discount, note: 'sale' };
}

// A read of a field that the object leaves out gives undefined, which `??`
// replaces.
export function cost(item: Item): bigint {
  return item.price - (item.discount ?? 0n);
}

export function bestDiscount(a: Item, b: Item): bigint {
  return a.discount ?? b.discount ?? 0n;
}

export function hasNote(item: Item): boolean {
  return item.note !== undefined;
}

export function plain(item: Item): boolean {
  const d = item.discount;
  return undefined === d;
}
