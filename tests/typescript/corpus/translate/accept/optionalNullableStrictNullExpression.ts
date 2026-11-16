// certify: required
function nullFlag(x?: bigint | null): boolean { return x === null; }
function missingFlag(x?: bigint): boolean { return x === undefined; }

export function f(x?: bigint | null): boolean {
  return x === null ? nullFlag(x) : missingFlag(x);
}

export function inverted(x?: bigint | null): boolean {
  return x !== null ? missingFlag(x) : nullFlag(x);
}

function sortedWithNull(xs: ReadonlyArray<number>, x?: bigint | null): number[] {
  return xs.toSorted((a, b) => a - b);
}

export function guardedSort(xs: ReadonlyArray<number>, x?: bigint | null): number[] {
  return x === null ? sortedWithNull(xs, x) : missingFlag(x) ? [] : [];
}
