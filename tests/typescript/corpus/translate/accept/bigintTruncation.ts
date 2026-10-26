// Both truncate toward zero, as JS does: -7n / 2n is -3n, -7n % 2n is -1n.
export function f(a: bigint): bigint { return a / 2n + a % -3n; }
