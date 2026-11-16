export interface JSNullish {
  readonly limit?: bigint | null;
}

export function effectiveLimit(s: JSNullish): bigint {
  return s.limit ?? 10n;
}

export function classify(limit?: bigint | null): bigint {
  if (limit === undefined) return 0n;
  if (limit === null) return 1n;
  return limit;
}

export function missing(): JSNullish {
  return {};
}

export function cleared(): JSNullish {
  return { limit: null };
}

export function set(): JSNullish {
  return { limit: 5n };
}
