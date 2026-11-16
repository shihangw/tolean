export interface Settings {
  readonly limit?: bigint | null;
}

export function effectiveLimit(s: Settings): bigint {
  return s.limit ?? 10n;
}

export function fieldIsStrictNull(s: Settings): boolean {
  return s.limit === null;
}

export function fieldIsLooseNull(s: Settings): boolean {
  return s.limit == null;
}

export function fieldIsUndefined(s: Settings): boolean {
  return s.limit === undefined;
}

export function parameterLimit(limit?: bigint | null): bigint {
  return limit ?? 10n;
}

export function classify(limit?: bigint | null): bigint {
  if (limit === undefined) return 0n;
  if (limit === null) return 1n;
  return limit;
}

export function isStrictNull(limit?: bigint | null): boolean {
  return limit === null;
}

export function isLooseNull(limit?: bigint | null): boolean {
  return limit == null;
}

export function isStrictUndefined(limit?: bigint | null): boolean {
  return limit === undefined;
}

export function nullOr(value?: bigint | null): boolean {
  return value === null || false;
}

export function notNullAnd(value?: bigint | null): boolean {
  return value !== null && true;
}

export function undefinedOr(value?: bigint | null): boolean {
  return value === undefined || false;
}

export function notUndefinedAnd(value?: bigint | null): boolean {
  return value !== undefined && true;
}

export function looseNarrow(limit?: bigint | null): bigint {
  if (limit != null) return limit;
  return 0n;
}

export function strictNarrow(limit?: bigint | null): bigint {
  if (limit !== null) return limit ?? 10n;
  return 0n;
}

export function unusedAfterNull(limit?: bigint | null): bigint {
  if (limit === null) return 1n;
  return 0n;
}

export function unusedAfterUndefined(limit?: bigint | null): bigint {
  if (limit === undefined) return 1n;
  return 0n;
}

export function cleared(): Settings {
  return { limit: null };
}

export function set(): Settings {
  return { limit: 5n };
}

export function callCleared(): bigint {
  return parameterLimit(null);
}

export function callMissing(): bigint {
  return parameterLimit(undefined);
}

export function callOmitted(): bigint {
  return parameterLimit();
}

export function callSet(): bigint {
  return parameterLimit(5n);
}

export interface Inner {
  readonly count: bigint | null;
}

export function projected(inner?: Inner | null): bigint {
  return inner?.count ?? 10n;
}

export interface OptionalInner {
  readonly count?: bigint | null;
}

export function projectedOptionalField(inner: OptionalInner | null): bigint {
  return inner?.count ?? 10n;
}

export function projectedOptionalReceiver(inner?: OptionalInner | null): bigint {
  return inner?.count ?? 10n;
}
