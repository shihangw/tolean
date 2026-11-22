// certify: required
export function nested(
  xs: ReadonlyArray<bigint | undefined>,
  ys: ReadonlyArray<bigint>,
): bigint {
  let n = 0n;
  for (const x of xs) {
    if (x !== undefined) {
      for (const y of ys) n += y;
      n += x;
      for (const y of ys) n += y;
    }
  }
  return n;
}
