export function anyOfZero(xs: ReadonlyArray<boolean>): boolean {
  return xs.reduce((a, x) => a || x, new Set<number>([0]).has(-0));
}

export function anyOfEntry(xs: ReadonlyArray<boolean>): boolean {
  return xs.reduce((a, x) => a || x, new Map<number, boolean>([[1, true]]).has(1));
}
