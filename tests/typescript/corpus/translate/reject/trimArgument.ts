// expect: 3:10 'trim' takes no arguments
export function f(s: string): string {
  return s.trim("x");
}
