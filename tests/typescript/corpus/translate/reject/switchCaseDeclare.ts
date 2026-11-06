// expect: 11:3 a case that declares a local needs braces, as in case 'a': { const n = 1n; return n; }
// The clauses share one scope, so Node refuses the second `n`.
export interface A {
  readonly kind: 'a';
}
export interface B {
  readonly kind: 'b';
}
export type U = A | B;
export function f(s: U): bigint {
  switch (s.kind) {
    case 'a': const n = 1n; return n;
    case 'b': const n = 2n; return n;
  }
}
