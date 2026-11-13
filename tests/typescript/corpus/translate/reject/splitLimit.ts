// expect: 4:10 'split' takes a string separator and perhaps a limit, an integer literal
// A limit that is not an integer literal is not supported.
export function f(s: string, n: number): ReadonlyArray<string> {
  return s.split(",", n);
}
