// expect: 5:1 'undefined' would hide the global undefined; choose another name
export interface Item {
  readonly x?: bigint;
}
function undefined(): bigint {
  return 1n;
}
export function f(i: Item): boolean {
  return i.x === undefined;
}
