// expect: 6:10 a local function may be called only as a statement of its own
export function f(x: bigint): bigint {
  function twice(): bigint {
    return x * 2n;
  }
  return twice() + 1n;
}
