// expect: 3:3 the tuple has only 2 elements
export function f(t: readonly [bigint, bigint]): bigint {
  const [a, b, c] = t;
  return a + b + c;
}
