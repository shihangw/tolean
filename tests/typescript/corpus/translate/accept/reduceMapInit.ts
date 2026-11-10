export function firstOf(xs: ReadonlyArray<boolean>): boolean {
  return xs.reduce((a, x) => a, new Map<bigint, boolean>().has(0n));
}

export function anyOf(xs: ReadonlyArray<boolean>): boolean {
  return xs.reduce((a, x) => a || x, new Set<bigint>().has(0n));
}

export function anyOfOne(xs: ReadonlyArray<boolean>): boolean {
  return xs.reduce((a, x) => a || x, new Set<bigint>([0n]).has(0n));
}

export function firstOfEmptyItems(xs: ReadonlyArray<boolean>): boolean {
  return xs.reduce((a, x) => a, new Set<bigint>([]).has(0n));
}

export function anyOfEntry(xs: ReadonlyArray<boolean>): boolean {
  return xs.reduce((a, x) => a || x, new Map<bigint, boolean>([[0n, true]]).has(0n));
}
