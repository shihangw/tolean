export type Kind = 'apple' | 'pear';
export type Counts = Record<Kind, bigint>;

export function first(xs: readonly [bigint, string] | null): bigint {
  return xs?.[0] ?? 7n;
}

export function last(xs?: readonly [bigint, string]): string {
  return xs?.[1] ?? 'missing';
}

export function record(c: Counts | null, k: Kind): bigint {
  return c?.[k] ?? 9n;
}

export function literal(c?: Counts): bigint {
  return c?.['pear'] ?? 0n;
}

export function shadowed(some: boolean, xs?: readonly [bigint, string]): bigint {
  return xs?.[0] ?? (some ? 1n : 0n);
}

export type MaybeCounts = Record<Kind, bigint | undefined>;

export function optionalValue(xs?: readonly [bigint | undefined, string]): bigint | undefined {
  return xs?.[0];
}

export function optionalRecordValue(c: MaybeCounts | null, k: Kind): bigint | undefined {
  return c?.[k];
}
