// certify: required
export function inferredSpread(xs: ReadonlyArray<bigint | null>, x: bigint): ReadonlyArray<bigint | null> {
  const values = [...xs, x ** 2n];
  return values;
}

export function typedSpread(xs: ReadonlyArray<bigint | null>, x: bigint): ReadonlyArray<bigint | null> {
  const values: ReadonlyArray<bigint | null> = [...xs, x ** 2n];
  return values;
}

export function bigintSpread(xs: ReadonlyArray<bigint>, x: bigint): ReadonlyArray<bigint> {
  const values = [...xs, x ** 2n];
  return values;
}
