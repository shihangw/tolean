// certify: required
interface Reading {
  readonly value: number;
  readonly label: string;
}

export function byValue(xs: ReadonlyArray<Reading>): Reading[] {
  return xs.toSorted((a, b) => (a.value < b.value) ? -1 : (a.value > b.value) ? 1 : 0);
}

export function numbers(xs: ReadonlyArray<number>): number[] {
  return xs.toSorted((a, b) => (a < b) ? -1 : (a > b) ? 1 : 0);
}
