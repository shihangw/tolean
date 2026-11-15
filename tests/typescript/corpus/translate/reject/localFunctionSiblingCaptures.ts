// expect: 6:3 a called sibling such as 'scale' must not capture variables yet
export function f(factor: bigint, x: bigint): bigint {
  function scale(value: bigint): bigint {
    return value * factor;
  }
  function apply(value: bigint): bigint {
    return scale(value);
  }
  return apply(x);
}
