// expect: 3:10 Date.parse needs a Date Time String Format literal
export function f(): number {
  return Date.parse("January 1, 2000");
}
