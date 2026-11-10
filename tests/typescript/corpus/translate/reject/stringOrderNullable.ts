// expect: 3:10 ordering needs two bigints, two numbers or two strings
export function f(s: string | null, t: string): boolean {
  return s < t;
}
