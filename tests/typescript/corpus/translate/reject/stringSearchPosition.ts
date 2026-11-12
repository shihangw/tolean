// expect: 4:10 'startsWith' takes a string and perhaps a position, an integer literal
// A position that is not an integer literal is not supported.
export function f(s: string, i: number): boolean {
  return s.startsWith("a", i);
}
