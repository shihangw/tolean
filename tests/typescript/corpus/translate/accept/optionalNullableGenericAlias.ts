type Maybe<T> = T | null;

export interface Settings {
  readonly value?: Maybe<bigint | null>;
}

export interface NestedSettings {
  readonly value?: Maybe<Maybe<bigint>>;
}

export function effectiveValue(s: Settings): bigint {
  return s.value ?? 10n;
}

export function nestedValue(s: NestedSettings): bigint {
  return s.value ?? 10n;
}

export function parameterValue(value?: Maybe<bigint | null>): bigint {
  return value ?? 10n;
}
