// expect: 4:3 a loop must be 'for (const [a, b] of xs)'
export function f(pairs: ReadonlyArray<readonly [bigint, bigint]>): bigint {
  let total = 0n;
  for (let [a, b] of pairs) {
    total += a + b;
  }
  return total;
}
