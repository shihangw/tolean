// expect: 7:3 a local function may not call another local function, such as 'one'
export function f(x: bigint): bigint {
  let n = 0n;
  function one(): void {
    n += 1n;
  }
  function two(): void {
    one();
    one();
  }
  two();
  return x + n;
}
