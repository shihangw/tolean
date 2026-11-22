// certify: required
export function twoReturning(
  xs: ReadonlyArray<bigint | undefined>,
  ys: ReadonlyArray<bigint | undefined>,
): boolean {
  for (const x of xs) {
    if (x === undefined) return true;
  }
  for (const y of ys) {
    if (y === undefined) return true;
  }
  return false;
}
