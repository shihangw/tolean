// expect: 3:3 nested patterns, defaults and rest elements are not supported
export function f(s: { a: { b: number } }): number {
  const { a: { b } } = s;
  return b;
}
