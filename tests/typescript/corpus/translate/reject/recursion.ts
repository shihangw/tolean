// expect: 2:47 calls may name only functions declared earlier in this file, or imported (no recursion)
export function f(x: bigint): bigint { return f(x); }
