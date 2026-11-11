// expect: 4:10 'startsWith' takes one string here; a position argument is not supported
// The position argument of startsWith is not supported.
export function f(s: string): boolean {
  return s.startsWith("a", 1);
}
