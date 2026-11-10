// expect: 2:63 unsupported statement
export function f(n: bigint): bigint { if (n < 0n) return 0n; throw n; }
