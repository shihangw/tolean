// expect: 4:3 a local function may not use 'ys', which the function around it owns
export function f(xs: Array<bigint>): bigint {
  const ys: Array<bigint> = [];
  function add(x: bigint): void {
    ys.push(x);
  }
  add(1n);
  return 0n;
}
