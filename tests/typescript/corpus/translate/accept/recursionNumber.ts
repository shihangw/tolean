export interface Item {
  readonly price: number;
  readonly rest: Item | null;
}

export function total(i: Item): number {
  const rest = i.rest;
  if (rest === null) return i.price;
  return i.price + total(rest);
}
