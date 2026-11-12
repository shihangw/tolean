// expect: 5:10 only parameters and locals may be referenced
export function f(x: bigint): bigint {
  let n = 0n;
  function bump(): void {
    n += m;
  }
  const m = x;
  bump();
  return n;
}
