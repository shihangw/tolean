// certify: required
export function total(r: Record<string, number | undefined>, keys: string[]): number {
  let sum = 0;
  for (const key of keys) {
    if (Object.hasOwn(r, key)) {
      sum += r[key] ?? 0;
    }
  }
  return sum;
}
