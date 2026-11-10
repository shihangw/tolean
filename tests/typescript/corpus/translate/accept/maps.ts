type Color = 'red' | 'green';

interface Sale {
  readonly item: string;
  readonly amount: bigint;
}

interface Tally {
  readonly counts: ReadonlyMap<string, bigint>;
  readonly total: bigint;
}

/** Adds up the amount of each item, in the order that each item first sold. */
export function totals(sales: ReadonlyArray<Sale>): Map<string, bigint> {
  const byItem = new Map<string, bigint>();
  for (const s of sales) {
    byItem.set(s.item, (byItem.get(s.item) ?? 0n) + s.amount);
  }
  return byItem;
}

export function tally(sales: ReadonlyArray<Sale>): Tally {
  const counts: Map<string, bigint> = new Map();
  let total = 0n;
  for (const s of sales) {
    if (!counts.has(s.item)) {
      counts.set(s.item, 0n);
    }
    counts.set(s.item, (counts.get(s.item) ?? 0n) + 1n);
    total += s.amount;
  }
  return { counts, total };
}

export function size(m: ReadonlyMap<string, bigint>): number {
  return m.size;
}

export function flagged(m: ReadonlyMap<bigint, boolean>, k: bigint): boolean {
  return m.has(k) && (m.get(k) ?? false);
}

export function shade(colors: ReadonlyMap<Color, string>): string {
  return colors.get('red') ?? colors.get('green') ?? 'none';
}

export function withoutKeys(keys: ReadonlyArray<string>): Map<string, bigint> {
  const m = new Map<string, bigint>();
  m.set('a', 1n);
  m.set('b', 2n);
  m.set('a', 3n);
  for (const k of keys) {
    m.delete(k);
  }
  return m;
}
