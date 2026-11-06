// expect: 4:3 '??=' needs a local declared with let, of a type T | null
export function f(x: bigint): bigint {
  let y = x;
  y ??= 1n;
  return y;
}
