// expect: 2:19 an optional parameter may not also be nullable
export function f(a?: bigint | null): bigint {
  return a ?? 0n;
}
