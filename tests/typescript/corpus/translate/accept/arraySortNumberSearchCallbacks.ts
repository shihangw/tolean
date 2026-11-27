// certify: required
function sorted(xs: ReadonlyArray<number>): number[] {
  return xs.toSorted((a, b) => a - b);
}
export function anySorted(xs: ReadonlyArray<ReadonlyArray<number>>): boolean {
  return xs.some(row => sorted(row).length > 1);
}
export function allSorted(xs: ReadonlyArray<ReadonlyArray<number>>): boolean {
  return xs.every(row => sorted(row).length > 0);
}
export function firstSorted(xs: ReadonlyArray<ReadonlyArray<number>>): ReadonlyArray<number> | undefined {
  return xs.find(row => sorted(row).length > 2);
}
export function indexSorted(xs: ReadonlyArray<ReadonlyArray<number>>): number {
  return xs.findIndex(row => sorted(row).length === 0);
}
