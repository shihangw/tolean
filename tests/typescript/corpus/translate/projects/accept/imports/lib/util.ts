// A file that other files import from.
export interface Gauge {
  readonly level: bigint;
  readonly max: bigint;
}

export function clamp(x: bigint, lo: bigint, hi: bigint): bigint {
  if (x < lo) return lo;
  if (x > hi) return hi;
  return x;
}
