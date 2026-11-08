// expect: 6:25 the callback of 'map' must give a value of a type that an array can hold
export interface Item {
  readonly label?: string;
}
export function f(items: ReadonlyArray<Item>): ReadonlyArray<string> {
  return items.map(i => i.label);
}
