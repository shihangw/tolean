// expect: 4:3 'down' calls itself
export function f(n: bigint): bigint {
  let sum = 0n;
  function down(k: bigint): void {
    sum += k;
    if (k > 0n) {
      down(k - 1n);
    }
  }
  down(n);
  return sum;
}
