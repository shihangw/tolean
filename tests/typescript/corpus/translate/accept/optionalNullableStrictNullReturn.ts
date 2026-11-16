// certify: required
export function f(x?: bigint | null): bigint | null {
  if (x === null) return x;
  return 1n;
}

export function differentPayload(x?: bigint | null): string | null {
  if (x === null) return x;
  return "value";
}

export function inverted(x?: bigint | null): bigint | null {
  if (x !== null) return 1n;
  return x;
}

function sortedWithNull(value: bigint | null, xs: ReadonlyArray<number>): number[] {
  return xs.toSorted((a, b) => a - b);
}

export function guardedSort(xs: ReadonlyArray<number>, x?: bigint | null): number[] {
  if (x === null) return sortedWithNull(x, xs);
  return [];
}
