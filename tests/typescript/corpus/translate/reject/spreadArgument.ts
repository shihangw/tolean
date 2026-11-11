// expect: 6:18 a spread '...' may only be an element of an array literal
function add(a: bigint, b: bigint): bigint {
  return a + b;
}
export function f(xs: ReadonlyArray<bigint>): bigint {
  return add(0n, ...xs);
}
