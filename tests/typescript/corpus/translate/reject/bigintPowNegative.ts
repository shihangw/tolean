// expect: 2:47 '**' needs two bigints and a bigint literal exponent
export function f(a: bigint): bigint { return a ** -1n; }
