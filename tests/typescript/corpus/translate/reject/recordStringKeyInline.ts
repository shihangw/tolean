// expect: 2:40 Record<string, V> is not supported yet: dynamic string lookup needs a certificate condition for inherited Object.prototype properties; naming the Record does not remove this requirement
export function countOf(counts: Record<string, number>, key: string): number {
  return counts[key] ?? 0;
}
