// expect: 3:11 computed property names are not supported
export function f(s: { a: number }): number {
  const { ["a"]: x } = s;
  return x;
}
