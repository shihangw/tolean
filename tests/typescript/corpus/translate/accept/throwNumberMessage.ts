// The message of an error is the only place that uses numbers, so the file is
// still generic over the number type.
export function fail(n: bigint): bigint {
  if (n < 0n) throw new Error(Number.isNaN(NaN) ? "nan" : "other");
  throw new Error(1 < 2 ? "small" : "large");
}
