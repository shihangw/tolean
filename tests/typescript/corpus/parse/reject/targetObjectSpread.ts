// expect: 4:39 the target ES2017 does not have object spread '...' (added in ES2018)
// target: ES2017
export interface P { readonly x: boolean; }
export function f(p: P): P { return { ...p, x: true }; }
