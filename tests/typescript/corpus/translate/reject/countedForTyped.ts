// expect: 2:51 the variable of a counted loop must be a number
export function f(n: number): number { let s = 0; for (let i: bigint = 0; i < n; i++) { s = s + 1; } return s; }
