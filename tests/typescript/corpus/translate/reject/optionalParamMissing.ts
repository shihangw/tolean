// expect: 6:10 'f' takes 1 to 2 arguments
function f(a: bigint, b?: bigint): bigint {
  return a + (b ?? 0n);
}
export function g(): bigint {
  return f();
}
