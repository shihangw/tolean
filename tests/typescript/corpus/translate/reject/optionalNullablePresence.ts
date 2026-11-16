export interface Settings {
  readonly limit?: bigint | null;
}

export function ownsLimit(s: Settings): boolean {
  return "limit" in s;
}
