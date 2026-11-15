// expect: 3:10 a dynamic length can throw RangeError, whose engine-defined message is not modeled
export function f(s: string, n: number): string {
  return s.padStart(n, "x");
}
