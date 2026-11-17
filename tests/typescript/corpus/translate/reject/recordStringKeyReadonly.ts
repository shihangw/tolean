// expect: 2:38 Record<string, V> is not supported yet: dynamic string lookup needs a certificate condition for inherited Object.prototype properties; naming the Record does not remove this requirement
export type Counts = Readonly<Record<string, number>>;
export function countOf(counts: Counts, key: string): number {
  return counts[key] ?? 0;
}
