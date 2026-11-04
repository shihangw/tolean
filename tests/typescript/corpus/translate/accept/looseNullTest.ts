export function total(x: bigint | null, y: bigint | null): bigint {
  let sum = 0n;
  if (x != null) {
    sum += x;
  }
  if (y == null) return sum;
  return sum + y;
}

export function positiveOrMissing(x: bigint | null): boolean {
  return x == null || x > 0n;
}

export function present(x: bigint | null): boolean {
  return null != x;
}
