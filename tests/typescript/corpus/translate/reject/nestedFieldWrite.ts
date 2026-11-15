// expect: 5:3 an expression statement must assign a let local
interface P { x: number; }
interface Box { point: P; }
export function f(b: Box): number {
  b.point.x = 1;
  return b.point.x;
}
