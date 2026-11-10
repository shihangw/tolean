// expect: 2:69 tolean supports only 'throw new Error(message)'
export function f(n: bigint): bigint { if (n < 0n) return 0n; throw n; }
