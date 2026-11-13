interface P { readonly x: bigint }
// expect: 3:49 Object.is needs two numbers, or two values of one primitive type
export function f(a: P, b: P): boolean { return Object.is(a, b); }
