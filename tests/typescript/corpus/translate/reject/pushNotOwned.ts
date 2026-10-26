// expect: 2:48 push is allowed only onto an owned array, one element at a time
export function f(xs: Array<bigint>): bigint { xs.push(1n); return 0n; }
