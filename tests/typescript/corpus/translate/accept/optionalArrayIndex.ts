export interface Samples {
  readonly values?: ReadonlyArray<bigint>;
}

export function nullable(xs: ReadonlyArray<bigint> | null): bigint {
  return xs?.[0] ?? 7n;
}

export function optional(xs?: ReadonlyArray<bigint>): bigint {
  return xs?.[1] ?? 9n;
}

export function field(samples: Samples): bigint | undefined {
  return samples.values?.[0];
}
