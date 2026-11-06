// expect: 7:23 'discount' does not have the field's type
interface Item {
  readonly price: bigint;
  readonly discount?: bigint;
}
export function f(i: Item): Item {
  return { price: 1n, discount: i.discount };
}
