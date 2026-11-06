// expect: 7:10 compare it with === undefined
interface Item {
  readonly price: bigint;
  readonly discount?: bigint;
}
export function f(i: Item): boolean {
  return i.discount == null;
}
