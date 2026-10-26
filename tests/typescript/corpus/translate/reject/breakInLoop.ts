// expect: 2:68 a loop body may not return, break or continue
export function f(xs: ReadonlyArray<bigint>): bigint { let s = 0n; for (const x of xs) { if (x > 0n) { break; } s += x; } return s; }
