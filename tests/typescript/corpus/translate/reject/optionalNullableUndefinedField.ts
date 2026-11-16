// expect: 7:19 undefined may stand only where an optional value is expected
export interface Settings {
  readonly limit?: bigint | null;
}

export function explicitUndefined(): Settings {
  return { limit: undefined };
}
