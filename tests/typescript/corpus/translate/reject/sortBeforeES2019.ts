// target: ES2018
// expect: 5:10 the target ES2018 does not have a stable Array.prototype.sort
// Array.prototype.sort is stable from ES2019.
export function f(xs: ReadonlyArray<string>): string[] {
  return [...xs].sort((a, b) => (a < b) ? -1 : (a > b) ? 1 : 0);
}
