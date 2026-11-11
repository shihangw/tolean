// expect: 4:3 destructuring an array of nullable values could give null or undefined
export function f(rows: ReadonlyArray<ReadonlyArray<bigint | null>>): bigint {
  let total = 0n;
  for (const [a] of rows) {
    total += a ?? 0n;
  }
  return total;
}
