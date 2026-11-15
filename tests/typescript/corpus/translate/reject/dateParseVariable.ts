// expect: 3:10 Date.parse needs a Date Time String Format string literal
export function f(s: string): number {
  return Date.parse(s);
}
