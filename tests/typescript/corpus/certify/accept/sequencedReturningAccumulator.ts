// certify: required
export function returningAccumulator(
  xs: ReadonlyArray<bigint | undefined>,
  ys: ReadonlyArray<bigint | null>,
): bigint {
  let n = 0n;
  for (const x of xs) {
    if (x === undefined) return n;
    n += x;
  }
  n += 1n;
  for (const y of ys) {
    if (y === null) return n;
    n += y;
  }
  return n;
}
