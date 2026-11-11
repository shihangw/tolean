// expect: 4:10 the argument of 'includes' must be a string
// JS would convert the number with ToString first.
export function f(s: string, n: number): boolean {
  return s.includes(n);
}
