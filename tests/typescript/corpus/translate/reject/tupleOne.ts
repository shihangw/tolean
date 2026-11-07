// expect: 2:22 a tuple needs two elements or more
export function f(t: [bigint]): bigint {
  return 0n;
}
