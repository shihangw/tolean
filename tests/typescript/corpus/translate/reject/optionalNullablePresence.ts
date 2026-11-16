// expect: 7:10 unsupported binary operator
export interface Settings {
  readonly limit?: bigint | null;
}

export function ownsLimit(s: Settings): boolean {
  return "limit" in s;
}
