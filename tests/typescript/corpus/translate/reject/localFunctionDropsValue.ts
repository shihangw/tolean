// expect: 6:3 a call of 'twice' as a statement drops its value
export function f(x: bigint): bigint {
  function twice(): bigint {
    return x * 2n;
  }
  twice();
  return x;
}
