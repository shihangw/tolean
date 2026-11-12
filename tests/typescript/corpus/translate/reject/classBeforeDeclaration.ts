// expect: 3:58 declare the error class before the function that throws it
// JS does not hoist a class, so a function above it cannot throw it.
export function f(n: bigint): bigint { if (n < 0n) throw new Late("x"); return n; }
class Late extends Error {}
