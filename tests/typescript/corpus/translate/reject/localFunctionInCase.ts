// expect: 4:3 a local function must stand in the body of the function around it
export function f(x: bigint): bigint {
  let t = 0n;
  if (x > 0n) {
    switch (x) {
      case 1n: {
        function bump(k: bigint): void {
          t += k * x;
        }
        bump(1n);
      }
    }
  }
  return t;
}
