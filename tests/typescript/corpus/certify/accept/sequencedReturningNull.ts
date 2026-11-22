// certify: required
export function twoReturning(
  xs: ReadonlyArray<bigint | null>,
  ys: ReadonlyArray<bigint | null>,
): boolean {
  for (const x of xs) {
    if (x === null) return true;
  }
  for (const y of ys) {
    if (y === null) return true;
  }
  return false;
}
