// expect: 7:13 a local function may be called only as a statement of its own
export function f(xs: ReadonlyArray<bigint>): bigint {
  let sum = 0n;
  function add(x: bigint): void {
    sum += x;
  }
  const g = add;
  return sum;
}
