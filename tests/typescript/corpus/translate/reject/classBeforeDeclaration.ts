// expect: 3:58 declare the error class before the function that throws it
// A throw names only a class declared above its function, as a call names only a function declared earlier.
export function f(n: bigint): bigint { if (n < 0n) throw new Late("x"); return n; }
class Late extends Error {}
