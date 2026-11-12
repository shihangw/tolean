// expect: 7:32 '||' needs two booleans
interface P {
  readonly x: number;
  readonly y: number;
}
export function f(ps: ReadonlyArray<P>): P[] {
  return ps.toSorted((a, b) => (a.x - b.x) || (a.y - b.y));
}
