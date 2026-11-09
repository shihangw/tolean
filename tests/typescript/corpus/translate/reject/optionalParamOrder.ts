// expect: 2:31 a required parameter may not follow an optional one
export function f(a?: bigint, b: bigint): bigint {
  return b;
}
