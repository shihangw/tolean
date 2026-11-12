// expect: 7:32 a comparator here must compare keys
interface P {
  readonly x: number;
  readonly y: number;
}
export function f(ps: ReadonlyArray<P>): P[] {
  return ps.toSorted((a, b) => a.x - b.y);
}
