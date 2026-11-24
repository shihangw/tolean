// certify: required
export type Counts = Readonly<Record<string, number>>;

export function inlineCount(counts: Record<string, number>, key: string): number {
  if (Object.hasOwn(counts, key)) {
    return counts[key] ?? 0;
  }
  return 0;
}

export function guardedCount(counts: Counts, key: string): number {
  if (Object.hasOwn(counts, key)) {
    return counts[key] ?? 0;
  }
  return 0;
}

export function seed(): Counts {
  return { apples: 3, pears: 1 };
}

export function empty(): Counts {
  return {};
}

export type OptionalCounts = Readonly<Record<string, number | undefined>>;

export function optionalCount(counts: OptionalCounts, key: string): number | undefined {
  if (Object.hasOwn(counts, key)) {
    return counts[key];
  }
  return undefined;
}
