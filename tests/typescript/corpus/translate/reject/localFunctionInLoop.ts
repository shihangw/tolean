// expect: 6:5 a local function must stand in the body of the function around it
export function f(xs: ReadonlyArray<bigint>): bigint {
  let sum = 0n;
  for (const x of xs) {
    sum += x;
    function add(): void {
      sum += x;
    }
    add();
  }
  return sum;
}
