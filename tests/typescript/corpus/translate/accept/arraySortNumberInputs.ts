// certify: required
interface Input {
  readonly values: ReadonlyArray<number>;
}
export function field(input: Input): number[] {
  return input.values.toSorted((a, b) => a - b);
}
function sorted(xs: ReadonlyArray<number>): number[] {
  return xs.toSorted((a, b) => a - b);
}
export function appended(xs: ReadonlyArray<number>, ys: ReadonlyArray<number>): number[] {
  return sorted([...xs, ...ys]);
}
export function copied(xs: ReadonlyArray<number>, ys: ReadonlyArray<number>): number[] {
  return [...xs, ...ys].sort((a, b) => a - b);
}
export function forwarded(xs: ReadonlyArray<number>, ys: ReadonlyArray<number>): number[] {
  return copied(xs, ys);
}
