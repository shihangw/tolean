import type { Shape, ShapeAlias } from './shape.ts';

export function hasKind(shape: Shape, kind: ShapeAlias['kind']): boolean {
  return shape.kind === kind;
}

export function label(shape: Shape): Shape['label'] {
  return shape.label;
}
