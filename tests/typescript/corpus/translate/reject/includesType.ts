// expect: 3:10 the argument of 'includes' must have the element type of the array
export function f(xs: ReadonlyArray<bigint>, n: number): boolean {
  return xs.includes(n);
}
