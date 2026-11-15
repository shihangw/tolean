// expect: 4:3 an expression statement must assign a let local
interface P { x: number; }
export function f(p: P): number {
  p.x += 1;
  return p.x;
}
