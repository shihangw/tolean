export interface Options {
  readonly limit: number | null;
  readonly label: string | null;
}

export function limitOf(o: Options, fallback: number | null): number {
  return o.limit ?? fallback ?? 10;
}

export function labelOf(o: Options): string {
  return o.label ?? "none";
}

export function firstSet(a: bigint | null, b: bigint | null): bigint | null {
  return a ?? b;
}
