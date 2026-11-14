// expect: number-key certificates currently require one key
interface Pair {
  readonly x: number;
  readonly y: number;
}
export function f(xs: ReadonlyArray<Pair>): Pair[] {
  return xs.toSorted((a, b) => (a.x < b.x) ? -1 : (a.x > b.x) ? 1 : a.y - b.y);
}
