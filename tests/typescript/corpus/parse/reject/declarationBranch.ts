// expect: 3:10 needs a block around it
export function f(a: boolean): void {
  if (a) const b = 1
}
