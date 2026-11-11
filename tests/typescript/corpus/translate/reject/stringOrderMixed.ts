// expect: 3:10 ordering needs two bigints, two numbers or two strings
export function f(s: string, n: bigint): boolean {
  return s < n;
}
