// expect: 4:3 an expression statement must assign a let local
interface P { x: number; }
export function f(p: P): number {
  --p.x;
  return p.x;
}
