// expect: 6:3 a case that declares a local needs braces
export interface A { readonly kind: 'a'; }
export interface B { readonly kind: 'b'; }
export type U = A | B;
export function f(s: U, xs: ReadonlyArray<bigint>): bigint {
  switch (s.kind) {
    case 'a': const [n] = xs; return n ?? 1n;
    case 'b': const [n] = xs; return n ?? 2n;
  }
}
