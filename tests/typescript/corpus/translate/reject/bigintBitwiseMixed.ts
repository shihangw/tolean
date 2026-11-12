// expect: 2:58 '&' needs two bigints
export function f(a: bigint, b: number): bigint { return a & b; }
