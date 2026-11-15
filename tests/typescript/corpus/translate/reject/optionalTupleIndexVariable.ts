// expect: 3:15 the index of a tuple must be a number literal, such as t[0]
export function f(i: number, xs?: readonly [bigint, string]): bigint {
  return xs?.[i] ?? 0n;
}
