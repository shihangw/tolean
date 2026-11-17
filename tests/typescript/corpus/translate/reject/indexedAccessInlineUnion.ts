// expect: 3:18 a literal union needs a name
export interface Shape {
  readonly kind: 'circle' | 'square';
}
export function hasKind(s: Shape, kind: Shape['kind']): boolean {
  return s.kind === kind;
}
