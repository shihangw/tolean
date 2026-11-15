// expect: 4:10 unsupported expression
interface P { x: number; }
export function f(p: P): number {
  return p.x = 1;
}
