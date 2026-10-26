function g(x: bigint): bigint { return Number.isNaN(NaN) ? x : x; }
export function f(x: bigint): bigint { return g(x); }
