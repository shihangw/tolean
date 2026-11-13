// expect: 3:58 'TooMany' takes 2 arguments
class TooMany extends Error { constructor(readonly limit: bigint, extra: string) { super(extra); } }
export function f(n: bigint): bigint { if (n > 9n) throw new TooMany(n); return n; }
