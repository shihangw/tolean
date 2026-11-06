// expect: 2:22 a union of primitive types needs a name
export function f(x: string | bigint): bigint {
  if (typeof x === 'string') return 0n;
  return x;
}
