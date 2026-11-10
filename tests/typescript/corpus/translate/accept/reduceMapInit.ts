export function firstOf(xs: ReadonlyArray<boolean>): boolean {
  return xs.reduce((a, x) => a, new Map<bigint, boolean>().has(0n));
}

export function anyOf(xs: ReadonlyArray<boolean>): boolean {
  return xs.reduce((a, x) => a || x, new Set<bigint>().has(0n));
}
