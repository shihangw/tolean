// certify: required
export function threeReturning(
  xs: ReadonlyArray<bigint | undefined>,
  ys: ReadonlyArray<bigint | null>,
  zs: ReadonlyArray<bigint | undefined>,
): bigint {
  for (const x of xs) {
    if (x === undefined) return 1n;
  }
  for (const y of ys) {
    if (y === null) return 2n;
  }
  for (const z of zs) {
    if (z === undefined) return 3n;
  }
  return 0n;
}
