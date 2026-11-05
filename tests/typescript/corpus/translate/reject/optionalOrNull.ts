// expect: 7:13 the branches of '?:' have different types
// The output has one `none` for both a missing field and `null`.
export interface Item {
  readonly x?: bigint;
}
export function f(i: Item, b: boolean): boolean {
  const d = b ? i.x : null;
  return d === null;
}
