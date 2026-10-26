// expect: 2:57 unsupported expression
export function f(x: bigint): bigint { const ignored = (x = 1n) === null; return x; }
