// expect: 7:10 a comparator proof obligation currently requires bigint elements
interface P {
  readonly x: number;
  readonly y: number;
}
export function f(ps: ReadonlyArray<P>): P[] {
  return ps.toSorted((a, b) => a.x - b.y);
}
