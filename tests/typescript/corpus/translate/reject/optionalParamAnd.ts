// expect: 3:29 ordering needs two bigints or two numbers
export function f(a?: bigint): boolean {
  return a !== undefined && a > 0n;
}
