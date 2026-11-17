// expect: 6:46 indexed access types are not supported
export interface Shape {
  readonly kind: 'circle' | 'square';
  readonly size: number;
}
export function hasKind(s: Shape, kind: Shape['kind']): boolean {
  return s.kind === kind;
}
