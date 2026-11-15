// expect: 4:10 'includes' takes a string and perhaps a number position
// JS would convert the number with ToString first.
export function f(s: string, n: number): boolean {
  return s.includes(n);
}
