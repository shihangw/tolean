// expect: a dynamic Record read must be guarded by Object.hasOwn on the same record and key
type Counts = Record<string, number>;

export function total(r: Counts, keys: string[]): number {
  let sum = 0;
  for (const key of keys) {
    sum += r[key] ?? 0;
  }
  return sum;
}
