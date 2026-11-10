// expect: 2:68 the message of an Error must be a string
export function f(n: bigint): bigint { if (n < 0n) throw new Error(n); return n; }
