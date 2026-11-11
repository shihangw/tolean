// expect: 4:3 unsupported statement
export function total(xs: ReadonlyArray<bigint>): bigint {
  let sum = 0n;
  function add(x: bigint): void {
    sum += x;
  }
  for (const x of xs) {
    add(x);
  }
  return sum;
}
