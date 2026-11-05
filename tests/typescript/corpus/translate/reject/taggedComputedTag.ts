// expect: 5:54 a tag field must be its string literal itself
interface A { readonly kind: 'a'; readonly n: bigint; }
interface B { readonly kind: 'b'; readonly n: bigint; }
type U = A | B;
export function f(flag: boolean): A { return { kind: flag ? 'a' : 'a', n: 1n }; }
