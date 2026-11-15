// expect: 3:10 an optional tuple index could give null or undefined
export function f(xs?: readonly [bigint | null, string]): bigint {
  return xs?.[0] ?? 0n;
}
