export interface Shape {
  readonly kind: 'circle' | 'square';
  readonly size: number;
}
export function hasKind(s: Shape, kind: Shape['kind']): boolean {
  return s.kind === kind;
}
interface Inner { readonly value: bigint; }
interface Outer { readonly inner: Inner; }
type Leaf = Outer['inner']['value'];
type Values = Outer['inner']['value'][];
type GenericField<T> = T['kind'];
