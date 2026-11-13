// expect: 4:10 the target ES2016 does not have String.prototype.padStart and padEnd (added in ES2017)
// target: ES2016
export function f(s: string): string {
  return s.padStart(4, "0");
}
