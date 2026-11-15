// expect: 4:10 calls may name only
interface P { x: number; }
export function f(p: P): P {
  return Object.defineProperty(p, "x", { value: 1 });
}
