export interface Point {
  readonly value: bigint;
}

export function indexed(xs: ReadonlyArray<bigint> | null, i: number): bigint {
  return xs?.[i] ?? 7n;
}

export function chained(i: number, xs?: ReadonlyArray<Point>): bigint {
  return xs?.[i]?.value ?? 0n;
}
