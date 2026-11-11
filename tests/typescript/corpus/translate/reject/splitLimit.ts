// expect: 4:10 'split' takes one string here; a limit is not supported
// The limit of split is not supported.
export function f(s: string): ReadonlyArray<string> {
  return s.split(",", 2);
}
