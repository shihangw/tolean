// expect: 4:10 '+' on a string needs a string, a bigint or a boolean on the other side
// ToString of a number is not modelled yet.
export function f(s: string, n: number): string {
  return s + n;
}
