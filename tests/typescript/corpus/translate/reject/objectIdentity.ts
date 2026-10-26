// expect: 3:49 === here would compare objects or nullable values; only primitives and null tests are supported
interface P { readonly x: bigint }
export function f(a: P, b: P): boolean { return a === b; }
