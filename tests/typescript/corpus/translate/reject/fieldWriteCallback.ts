// expect: 4:23 unsupported expression
interface P { x: number; }
export function f(ps: ReadonlyArray<P>): ReadonlyArray<number> {
  return ps.map(p => (p.x = 1));
}
