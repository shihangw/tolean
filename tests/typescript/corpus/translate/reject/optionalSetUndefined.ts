// expect: 7:33 undefined may stand only where an optional value is expected
interface Item {
  readonly price: bigint;
  readonly discount?: bigint;
}
export function f(): Item {
  return { price: 1n, discount: undefined };
}
