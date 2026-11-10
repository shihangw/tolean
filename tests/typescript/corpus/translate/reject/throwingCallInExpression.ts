// expect: 3:47 'check' can throw, so a call of it must be the whole value
function check(n: bigint): bigint { if (n < 0n) throw new Error("negative"); return n; }
export function f(n: bigint): bigint { return check(n) + 1n; }
