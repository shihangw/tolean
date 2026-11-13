// expect: 3:63 'check' can throw, so a call of it may not stand in a branch of ?:
function check(n: bigint): bigint { if (n < 0n) throw new Error("negative"); return n; }
export function f(n: bigint, c: boolean): bigint { return c ? check(n) : 0n; }
