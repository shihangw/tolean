// target: ES2022
// expect: 5:10 the target ES2022 does not have Array.prototype.toSorted
// Array.prototype.toSorted is in ES2023.
export function f(xs: ReadonlyArray<string>): string[] {
  return xs.toSorted((a, b) => (a < b) ? -1 : (a > b) ? 1 : 0);
}
