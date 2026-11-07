// expect: 2:98 code after break is unreachable
export function f(xs: ReadonlyArray<bigint>): bigint { let s = 0n; for (const x of xs) { s += x; break; s += 1n; } return s; }
