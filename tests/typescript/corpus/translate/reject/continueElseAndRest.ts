// expect: 2:90 after an if whose first branch ends in continue
export function f(xs: ReadonlyArray<bigint>): bigint { let s = 0n; for (const x of xs) { if (x > 0n) continue; else { s += 1n; } s += x; } return s; }
