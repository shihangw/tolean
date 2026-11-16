export function f(a?: bigint): boolean {
  return a !== undefined && a > 0n;
}
