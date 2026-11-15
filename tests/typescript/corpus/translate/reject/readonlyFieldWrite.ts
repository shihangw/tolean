// expect: 4:3 an expression statement must assign a let local
export interface Point { readonly x: number; }
export function move(p: Point): number {
  p.x = 1;
  return p.x;
}
