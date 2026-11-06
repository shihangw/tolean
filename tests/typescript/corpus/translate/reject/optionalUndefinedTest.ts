// expect: 7:10 only the value of an optional field can be undefined here
interface Item {
  readonly price: bigint;
  readonly discount?: bigint;
}
export function f(i: Item): boolean {
  return i.price === undefined;
}
