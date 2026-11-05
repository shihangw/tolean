// expect: 5:47 a tag field may be read only in a test of its union, such as x.kind === 'circle'
interface Circle { readonly kind: 'circle'; readonly r: bigint; }
interface Square { readonly kind: 'square'; readonly side: bigint; }
type Shape = Circle | Square;
export function f(c: Circle): string { return c.kind; }
