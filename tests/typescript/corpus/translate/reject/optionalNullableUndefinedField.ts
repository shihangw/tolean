export interface Settings {
  readonly limit?: bigint | null;
}

export function explicitUndefined(): Settings {
  return { limit: undefined };
}
