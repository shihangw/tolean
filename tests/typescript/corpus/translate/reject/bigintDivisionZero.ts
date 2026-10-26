// expect: 2:47 '/' and '%' need two bigints and a nonzero bigint literal divisor (JS throws on 0n)
export function f(a: bigint): bigint { return a / 0n; }
