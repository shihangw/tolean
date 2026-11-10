// target: ES2015
// expect: 6:10 the target ES2015 does not have the white space of String.prototype.trim without U+180E
// ES2015 names Unicode 5.1, where U+180E is white space, so trim removes it
// there. Later editions name Unicode 8.0 or later, where it is not.
export function f(s: string): string {
  return s.trim();
}
