// expect: 4:3 a local function that returns a value may not change a variable
export function f(x: bigint): bigint {
  let n = 0n;
  function bump(): bigint {
    n += 1n;
    return n;
  }
  const y = bump();
  return x + y;
}
