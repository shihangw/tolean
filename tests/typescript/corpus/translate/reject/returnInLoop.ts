// expect: 2:117 a loop body may return only where the statements after the loop end in a return
export function f(xs: ReadonlyArray<bigint>, ys: ReadonlyArray<bigint>): bigint { let s = 0n; for (const x of xs) { for (const y of ys) { if (y > x) return y; } s += x; } return s; }
