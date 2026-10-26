interface P { readonly x: bigint }
export function f(a: P, b: P): boolean { return a === b; }
