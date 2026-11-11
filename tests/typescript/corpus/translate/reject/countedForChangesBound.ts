// expect: 2:51 change what its bound reads
export function f(n: number): number { let m = n; for (let i = 0; i < m; i++) { m = m - 1; } return m; }
