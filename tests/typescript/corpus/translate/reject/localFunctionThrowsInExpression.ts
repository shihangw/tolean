// expect: 10:3 a local function may not throw
function check(k: bigint): bigint {
  if (k < 0n) {
    throw new Error("negative");
  }
  return k;
}
export function f(x: bigint): bigint {
  let t = 0n;
  function bump(k: bigint): void {
    t += check(k);
  }
  bump(x);
  return t;
}
