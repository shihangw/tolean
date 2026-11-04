// expect: 5:46 the tag here must be 'circle'
interface Circle { readonly kind: 'circle'; readonly r: bigint; }
interface Square { readonly kind: 'square'; readonly side: bigint; }
type Shape = Circle | Square;
export function f(): Circle { return { kind: 'square', r: 1n }; }
