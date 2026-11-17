// certify: required
export type Kind = 'circle' | 'square';
export interface Shape {
  readonly kind: Kind;
  readonly size: bigint;
}
export interface Envelope {
  readonly shape: Shape;
}
export type ShapeAlias = Shape;
export type ShapeKind = ShapeAlias['kind'];

export function hasKind(s: Shape, kind: Shape['kind']): boolean {
  return s.kind === kind;
}

export function nested(s: Envelope, kind: Envelope['shape']['kind']): boolean {
  return s.shape.kind === kind;
}

export function size(s: Shape): Shape['size'] {
  return s.size;
}
