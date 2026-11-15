// expect: 4:10 calls may name only
interface P { x: number; }
export function f(p: P): P {
  return Object.assign(p, { x: 1 });
}
