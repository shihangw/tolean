export interface Point {
  x: number;
  readonly y: number;
}

export function sum(p: Point): number {
  return p.x + p.y;
}
