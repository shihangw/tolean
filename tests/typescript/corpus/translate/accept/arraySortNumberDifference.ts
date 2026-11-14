// certify: required
interface Sample {
  readonly value: number;
  readonly label: string;
}

export function byValue(xs: ReadonlyArray<Sample>): Sample[] {
  return xs.toSorted((a, b) => a.value - b.value);
}

export function descending(xs: ReadonlyArray<Sample>): Sample[] {
  return [...xs].sort((a, b) => b.value - a.value);
}

export function numbers(xs: ReadonlyArray<number>): number[] {
  return xs.toSorted((a, b) => a - b);
}

export function reverseComparison(xs: ReadonlyArray<number>): number[] {
  return xs.toSorted((a, b) => (a > b) ? -1 : (a < b) ? 1 : 0);
}
