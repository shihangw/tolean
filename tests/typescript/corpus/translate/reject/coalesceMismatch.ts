// expect: 2:59 the right side of '??' must have the type of the left side
export function f(x: bigint | null): bigint { return x ?? "none"; }
