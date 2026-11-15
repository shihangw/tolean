// target: ES2015
// expect: 4:10 Date.parse on the Date Time String Format
export function f(): number {
  return Date.parse("2000-01-01");
}
