export function comparisons(a: number, b: number, c: number, d: number, x: number, n: number) {
  const between = a < b && c > d;
  const bounded = x < n && n > 0;
  const logicalOr = a < b || c > d;
  const call = a < b && c > (d);
  const nested = a < b && c < d && x > n;
  const lineBreak = a < b && c >
    d;
  return between && bounded;
}
