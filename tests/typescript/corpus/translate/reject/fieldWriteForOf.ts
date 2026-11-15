// expect: 6:5 an expression statement must assign a let local
interface P { x: number; }
export function f(ps: ReadonlyArray<P>): number {
  let n = 0;
  for (const p of ps) {
    p.x = 1;
    n += p.x;
  }
  return n;
}
