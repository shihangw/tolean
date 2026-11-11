// target: ES2017
// expect: 7:12 the target ES2017 does not have object spread '...' (added in ES2018)
// Object spread is in ES2018. The interface has no bigint, which ES2017 would
// refuse first.
export interface P { readonly x: boolean; }
export function f(p: P): P {
  return { ...p, x: true };
}
