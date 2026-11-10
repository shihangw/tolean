// expect: 3:10 the string method 'lastIndexOf' is not supported here
export function f(s: string): number {
  return s.lastIndexOf("a");
}
