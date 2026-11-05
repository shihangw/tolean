// expect: 7:3 'undefined' would hide the function or global undefined in its whole block; choose another name
export interface Item {
  readonly x?: bigint;
}
export function f(i: Item): boolean {
  const b = i.x === undefined;
  const undefined = 1n;
  return b;
}
