// expect: 3:15 the tuple has no element 2
export function f(xs?: readonly [bigint, string]): bigint {
  return xs?.[2] ?? 0n;
}
