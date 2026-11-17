export type Counts = Readonly<Record<string, number>>;

export function countOf(counts: Counts, key: string): number {
  return counts[key] ?? 0;
}

export function inlineCount(counts: Record<string, number>, key: string): number {
  return counts[key] ?? 0;
}

export function readonlyCount(counts: Readonly<Record<string, number>>, key: string): number {
  return counts[key] ?? 0;
}

export function seed(): Counts {
  return { apples: 3, pears: 1 };
}

export function empty(): Counts {
  return {};
}
