// expect: 4:3 an expression statement must assign a let local
interface P { xs: Array<number>; }
export function f(p: P): number {
  p.xs.push(1);
  return p.xs.length;
}
