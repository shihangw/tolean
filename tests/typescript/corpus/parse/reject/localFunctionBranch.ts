// expect: 3:10 needs a block around it
export function f(a: boolean): void {
  if (a) function g(): void {}
}
