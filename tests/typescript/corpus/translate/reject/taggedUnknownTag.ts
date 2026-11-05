// expect: 5:37 'triangle' is not a tag of Shape here: { kind: 'triangle', r
interface Circle { readonly kind: 'circle'; readonly r: bigint; }
interface Square { readonly kind: 'square'; readonly side: bigint; }
type Shape = Circle | Square;
export function f(): Shape { return { kind: 'triangle', r: 1n }; }
