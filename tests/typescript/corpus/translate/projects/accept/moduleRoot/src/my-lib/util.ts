// Lean reads `my-lib` only as «my-lib».
export function inc(x: bigint): bigint {
  return x + 1n;
}
