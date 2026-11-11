// expect: 3:10 '+' on a string needs a string, a bigint or a boolean on the other side
export function f(s: string, t: string | null): string {
  return s + t;
}
