// expect: 6:3 a sibling call requires each captured variable to be named in its caller
export function f(factor: bigint, x: bigint): bigint {
  function scale(value: bigint): bigint {
    return value * factor;
  }
  function apply(value: bigint): bigint {
    return scale(value);
  }
  return apply(x);
}
