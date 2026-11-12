// expect: 9:25 an object's text depends on the order of its keys
// A caller may pass { y: 1, x: 2 } as a Point, which is the same Lean value
// as { x: 2, y: 1 }, but JSON.stringify writes the keys in their own order.
export interface Point {
  readonly x: number;
  readonly y: number;
}
export function render(p: Point): string {
  return JSON.stringify(p);
}
