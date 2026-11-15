// expect: 7:5 an expression statement must assign a let local
interface P { x: number; }
export function f(p: P): number {
  let n = 0;
  function g(): void {
    n += 1;
    p.x = 1;
  }
  g();
  return n;
}
