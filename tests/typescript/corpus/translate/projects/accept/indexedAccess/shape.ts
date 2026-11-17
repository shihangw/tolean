export type Kind = 'circle' | 'square';
export interface Shape {
  readonly kind: Kind;
  readonly size: bigint;
  readonly label?: string;
}
export type ShapeAlias = Shape;
