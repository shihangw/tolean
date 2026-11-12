// expect: 3:90 'check' can throw, so a call of it may not stand in a branch of ?:, after &&, || or ??, or in an arrow function
function check(n: bigint): bigint { if (n < 0n) throw new Error("negative"); return n; }
export function f(xs: ReadonlyArray<bigint>): ReadonlyArray<bigint> { return xs.map(x => check(x)); }
