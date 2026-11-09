// expect: 2:98 code after continue is unreachable
export function f(xs: ReadonlyArray<bigint>): bigint { let s = 0n; for (const x of xs) { s += x; continue; s += 1n; } return s; }
