// expect: 4:10 only parameters and locals may be referenced
interface P { x: number; }
export function f(p: P): boolean {
  return Reflect.set(p, "x", 1);
}
