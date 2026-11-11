// expect: 4:3 '+' on a string needs a string, a bigint or a boolean on the other side
export function f(n: number): string {
  let s = "";
  s += n;
  return s;
}
