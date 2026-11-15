// certify: required
export function rows(xs: ReadonlyArray<ReadonlyArray<number>>): number[][] {
  return xs.map(row => row.toSorted((a, b) => a - b));
}
export function appendedRows(xs: ReadonlyArray<ReadonlyArray<number>>): number[][] {
  return xs.map(row => [...row, 0].sort((a, b) => a - b));
}
export function captured(xs: ReadonlyArray<number>, ys: ReadonlyArray<number>): number[][] {
  return ys.map(_y => xs.toSorted((a, b) => a - b));
}
export function nested(xs: ReadonlyArray<ReadonlyArray<ReadonlyArray<number>>>): number[][][] {
  return xs.map(group => group.map(row => row.toSorted((a, b) => a - b)));
}
function sorted(xs: ReadonlyArray<number>): number[] {
  return xs.toSorted((a, b) => a - b);
}
export function called(xs: ReadonlyArray<ReadonlyArray<number>>): number[][] {
  return xs.map(row => sorted(row));
}
export function selected(xs: ReadonlyArray<ReadonlyArray<number>>): ReadonlyArray<number>[] {
  return xs.filter(row => sorted(row).length > 0);
}
