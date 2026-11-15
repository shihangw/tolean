// expect: 9:3 a called sibling may not call another local function yet
export function f(x: bigint): bigint {
  function first(value: bigint): bigint {
    return value + 1n;
  }
  function second(value: bigint): bigint {
    return first(value);
  }
  function third(value: bigint): bigint {
    return second(value);
  }
  return third(x);
}
