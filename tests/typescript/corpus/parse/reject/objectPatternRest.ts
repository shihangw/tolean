// expect: 3:3 nested patterns, defaults and rest elements are not supported
export function f(s: { a: number; b: number }): number {
  const { a, ...rest } = s;
  return a;
}
