// `map`, `filter`, `some`, `every` and `find` with an arrow function become
// the `List` functions with `fun`.
export interface Item {
  readonly name: string;
  readonly price: bigint;
  readonly active: boolean;
}

export interface Label {
  readonly text: string;
}

export function prices(items: ReadonlyArray<Item>): ReadonlyArray<bigint> {
  return items.map(i => i.price);
}

export function activeItems(items: ReadonlyArray<Item>): ReadonlyArray<Item> {
  return items.filter(i => i.active);
}

export function anyAbove(items: ReadonlyArray<Item>, limit: bigint): boolean {
  return items.some(i => i.price > limit);
}

export function allActive(items: ReadonlyArray<Item>): boolean {
  return items.every((i: Item) => i.active);
}

export function priceOf(items: ReadonlyArray<Item>, name: string): bigint {
  return items.find(i => i.name === name)?.price ?? 0n;
}

export function labels(items: ReadonlyArray<Item>): ReadonlyArray<Label> {
  return items.map(i => ({ text: i.name }));
}

export function bigOnes(xs: ReadonlyArray<number>): ReadonlyArray<number> {
  return xs.map(x => x + x).filter(x => x > 2);
}

export function firstOver(xs: ReadonlyArray<bigint>, limit: bigint): bigint {
  return xs.find(x => x > limit) ?? limit;
}
