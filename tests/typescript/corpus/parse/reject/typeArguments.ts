// expect: 3:17 tsc may read this '<'
export function f(a: number, b: number, c: number, d: number): void {
  const x = g(a < b, c > (d))
}
