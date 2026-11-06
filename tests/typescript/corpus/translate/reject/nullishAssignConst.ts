// expect: 3:3 '??=' needs a local declared with let, of a type T | null
export function f(x: bigint | null): bigint | null {
  x ??= 1n;
  return x;
}
