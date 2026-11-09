// expect: 3:12 the tuple has no element 2
export function f(t: [bigint, bigint]): bigint {
  return t[2];
}
