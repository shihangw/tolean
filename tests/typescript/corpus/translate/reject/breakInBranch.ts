// expect: 2:90 a branch that does not always return may not return, break or continue
export function f(xs: ReadonlyArray<bigint>): bigint { let s = 0n; for (const x of xs) { if (x > 0n) { if (x > 5n) break; s += x; } s += 1n; } return s; }
