// expect: 7:3 a called sibling such as 'one' must not capture variables yet
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
