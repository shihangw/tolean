// expect: 4:1 a union of interfaces needs a tag: a field that each of them has, with a different string literal type, such as kind: 'circle'
interface P { readonly x: bigint; }
interface Q { readonly y: bigint; }
type U = P | Q;
