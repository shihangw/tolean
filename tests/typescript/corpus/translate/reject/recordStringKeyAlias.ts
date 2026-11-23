// expect: 3:22 Record<string, V> is not supported yet: dynamic string lookup needs a certificate condition for inherited Object.prototype properties; naming the Record does not remove this requirement
type Key = string;
type Counts = Record<Key, number>;
export function countOf(counts: Counts, key: string): number {
  return counts[key] ?? 0;
}
