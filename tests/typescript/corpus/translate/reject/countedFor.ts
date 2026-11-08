// expect: 2:52 unsupported statement
export function f(n: bigint): bigint { let s = 0n; for (let i = 0n; i < n; i++) { s += i; } return s; }
