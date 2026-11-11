// target: ES2018
// expect: 5:10 the target ES2018 does not have String.prototype.trimStart and trimEnd
// String.prototype.trimStart is in ES2019.
export function f(s: string): string {
  return s.trimStart();
}
