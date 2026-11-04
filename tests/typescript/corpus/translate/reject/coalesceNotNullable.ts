// expect: 2:47 the left side of '??' is never null here
export function f(x: bigint): bigint { return x ?? 0n; }
