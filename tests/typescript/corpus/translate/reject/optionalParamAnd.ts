// expect: 3:29 ordering needs two bigints, two numbers or two strings
export function f(a?: bigint): boolean {
  return a !== undefined && a > 0n;
}
