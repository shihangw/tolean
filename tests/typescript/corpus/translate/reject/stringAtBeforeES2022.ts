// expect: 4:10 the target ES2021 does not have String.prototype.at (added in ES2022)
// target: ES2021
export function f(s: string): string {
  return s.at(-1) ?? "";
}
