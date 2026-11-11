// target: ES2015
// expect: 5:10 the target ES2015 does not have Array.prototype.includes
// Array.prototype.includes is in ES2016.
export function f(xs: ReadonlyArray<string>): boolean {
  return xs.includes('a');
}
