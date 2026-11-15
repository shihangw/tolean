// expect: 4:3 'delete' is not supported here
interface P { x?: number; }
export function f(p: P): number {
  delete p.x;
  return p.x ?? 0;
}
