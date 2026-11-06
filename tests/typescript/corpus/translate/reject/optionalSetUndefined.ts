// expect: 7:33 only parameters and locals may be referenced
interface Item {
  readonly price: bigint;
  readonly discount?: bigint;
}
export function f(): Item {
  return { price: 1n, discount: undefined };
}
