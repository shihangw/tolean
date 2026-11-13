// expect: 3:65 'check' can throw, so a call of it may not stand in a branch of ?:, after &&, || or ??
function check(n: bigint): bigint { if (n < 0n) throw new Error("negative"); return n; }
export function f(n: bigint, c: boolean): boolean { return c && check(n) > 0n; }
