// expect: 2:51 may not assign its variable
export function f(n: number): number { let s = 0; for (let i = 0; i < n; i++) { s = s + i; i = i + 1; } return s; }
