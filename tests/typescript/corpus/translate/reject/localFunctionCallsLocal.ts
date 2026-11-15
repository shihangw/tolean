// expect: 7:3 a sibling call requires each captured variable to be named in its caller
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
