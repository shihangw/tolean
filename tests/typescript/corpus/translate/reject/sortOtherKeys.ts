// expect: 7:10 a comparator proof obligation currently requires bigint elements
interface P {
  readonly x: bigint;
  readonly y: bigint;
}
export function f(ps: ReadonlyArray<P>): P[] {
  return ps.toSorted((a, b) => (a.x < b.y) ? -1 : (a.x > b.y) ? 1 : 0);
}
