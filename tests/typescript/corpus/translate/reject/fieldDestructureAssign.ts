// expect: 4:9 only a name, a property or an element can be assigned
interface P { x: number; }
export function f(p: P): number {
  [p.x] = [1];
  return p.x;
}
