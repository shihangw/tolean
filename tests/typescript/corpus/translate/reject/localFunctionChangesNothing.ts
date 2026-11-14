// expect: 3:3 a local function that returns nothing must change a let local
export function f(x: bigint): bigint {
  function nothing(): void {
  }
  nothing();
  return x;
}
