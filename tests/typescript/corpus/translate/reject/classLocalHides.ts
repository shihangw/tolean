// expect: 3:40 'NotFound' would hide the error class NotFound
class NotFound extends Error {}
export function f(n: bigint): bigint { const NotFound = n; return NotFound; }
