export function between(a: bigint, b: bigint, c: bigint, d: bigint): boolean {
  return a < b && c > d;
}

export function bounded(x: bigint, n: bigint): boolean {
  return x < n && n > 0n;
}

export function outside(a: bigint, b: bigint, c: bigint, d: bigint): boolean {
  return a < b || c > d;
}
