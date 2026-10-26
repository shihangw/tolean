// expect: 2:40 only a local declared with let may be assigned
export function f(x: bigint): bigint { x = 1n; return x; }
