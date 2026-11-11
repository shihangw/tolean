// expect: 3:3 a rest element on a tuple is not supported
export function f(t: readonly [bigint, bigint, bigint]): bigint {
  const [a, ...r] = t;
  return a + r[0];
}
