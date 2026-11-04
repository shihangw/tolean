// expect: 5:46 a field of a tagged union may be read only after a test of its tag
interface Circle { readonly kind: 'circle'; readonly r: bigint; }
interface Square { readonly kind: 'square'; readonly side: bigint; }
type Shape = Circle | Square;
export function f(s: Shape): bigint { return s.r; }
