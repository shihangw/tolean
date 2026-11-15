export interface Box {
  readonly value: bigint;
}

export function read(box: Box): bigint {
  return (Number.isNaN(NaN) ? null : box)?.value ?? 0n;
}
