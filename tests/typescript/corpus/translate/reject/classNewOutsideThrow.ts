// expect: 4:50 only new Date(t), new Map() and new Set() are supported
// An error is made only to be thrown.
class NotFound extends Error {}
export function f(n: bigint): bigint { const e = new NotFound("x"); return n; }
