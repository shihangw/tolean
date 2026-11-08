// expect: 4:24 unsupported expression
export function f(xs: ReadonlyArray<bigint>): boolean {
  let last = 0n;
  return xs.some(x => (last = x) > 0n);
}
