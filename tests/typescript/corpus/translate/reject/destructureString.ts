// expect: 3:3 destructuring needs a tuple, an array, a set or a map
export function f(s: string): string {
  const [c] = s;
  return c ?? '';
}
