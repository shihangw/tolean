// expect: a dynamic Record read must be guarded by Object.hasOwn on the same record and key; reads in callbacks and loops are not certified yet
type Counts = Record<string, number>;

export function counts(r: Counts, keys: string[]): number[] {
  return keys.map(k => r[k] ?? 0);
}
