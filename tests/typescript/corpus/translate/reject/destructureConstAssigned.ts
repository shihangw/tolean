// expect: 3:3 a name of the pattern is a const, and a later statement assigns it
export function f(t: readonly [bigint, bigint]): bigint {
  const [a, b] = t;
  a = b;
  return a;
}
