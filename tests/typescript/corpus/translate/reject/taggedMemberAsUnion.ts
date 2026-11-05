// expect: 6:52 the argument does not have the parameter's type
interface Circle { readonly kind: 'circle'; readonly r: bigint; }
interface Square { readonly kind: 'square'; readonly side: bigint; }
type Shape = Circle | Square;
export function area(s: Shape): bigint { if (s.kind === 'circle') return s.r; return s.side; }
export function g(c: Circle): bigint { return area(c); }
