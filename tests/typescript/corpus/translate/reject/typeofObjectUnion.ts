// expect: 6:7 typeof may only test, in an if, a local of a union of primitive types
interface A { readonly kind: 'a'; readonly x: bigint; }
interface B { readonly kind: 'b'; }
type U = A | B;
export function f(u: U): bigint {
  if (typeof u === 'object') return 1n;
  return 0n;
}
