// expect: 4:3 a literal tag is not stored in the Lean structure
export interface Point { readonly kind: "point"; readonly x: number; }
export function f(p: Point): string {
  const { kind } = p;
  return kind;
}
