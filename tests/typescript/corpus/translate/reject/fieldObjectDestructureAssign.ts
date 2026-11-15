// expect: 4:15 only a name, a property or an element can be assigned
interface P { x: number; }
export function f(p: P): number {
  ({ x: p.x } = { x: 1 });
  return p.x;
}
