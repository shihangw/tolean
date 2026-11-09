// expect: 2:68 a loop body may not return
export function f(xs: ReadonlyArray<bigint>): bigint { let s = 0n; for (const x of xs) { if (x > 0n) { return x; } s += x; } return s; }
