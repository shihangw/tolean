// expect: 2:58 '/' and '%' need two bigints and a nonzero bigint literal divisor (JS throws on 0n)
export function f(a: bigint, b: bigint): bigint { return a / b; }
