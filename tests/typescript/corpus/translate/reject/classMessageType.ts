// expect: 2:67 the message of an error must be a string
class Bad extends Error { constructor(readonly n: bigint) { super(n); } }
export function f(n: bigint): bigint { return n; }
