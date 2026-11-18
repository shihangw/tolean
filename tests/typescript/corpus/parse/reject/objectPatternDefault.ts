// expect: 3:13 default values are not supported
export function f(s: { a: number }): number {
  const { a = 1 } = s;
  return a;
}
