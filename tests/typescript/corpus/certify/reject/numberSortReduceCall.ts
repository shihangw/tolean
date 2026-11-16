// expect: sort conditions in this callback need an element-restricted link lemma
function sorted(xs: ReadonlyArray<number>): number[] {
  return xs.toSorted((a, b) => a - b);
}
export function f(xs: ReadonlyArray<ReadonlyArray<number>>): number {
  return xs.reduce((count, row) => count + sorted(row).length, 0);
}
