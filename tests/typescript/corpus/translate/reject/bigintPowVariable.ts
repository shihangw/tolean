// expect: 2:58 '**' needs two bigints and a bigint literal exponent
export function f(a: bigint, b: bigint): bigint { return a ** b; }
