// expect: 4:3 a local function needs a return type
export function f(x: bigint): bigint {
  let n = 0n;
  function bump() {
    n += x;
  }
  bump();
  return n;
}
