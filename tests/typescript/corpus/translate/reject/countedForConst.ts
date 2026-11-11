// expect: 2:51 a counted loop must be
export function f(n: number): number { let s = 0; for (const i = 0; i < n; i++) { s = s + i; } return s; }
