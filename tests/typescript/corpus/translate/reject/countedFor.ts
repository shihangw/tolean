// expect: 2:65 the start of a counted loop must be a number
export function f(n: bigint): bigint { let s = 0n; for (let i = 0n; i < n; i++) { s += i; } return s; }
