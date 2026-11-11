// expect: 3:10 'includes' does not take a callback here
export function f(xs: ReadonlyArray<boolean>): boolean {
  return xs.includes((x) => x);
}
