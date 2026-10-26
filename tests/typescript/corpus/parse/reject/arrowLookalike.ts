// expect: 4:3 tsc may read this '(…) {' as an arrow function
export function f(a: number): void {
  (a)
  {
    a += 1
  }
}
