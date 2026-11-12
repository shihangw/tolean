// expect: 7:32 a comparator here must compare keys
interface P {
  readonly x: bigint;
  readonly y: bigint;
}
export function f(ps: ReadonlyArray<P>): P[] {
  return ps.toSorted((a, b) => (a.x < b.y) ? -1 : (a.x > b.y) ? 1 : 0);
}
