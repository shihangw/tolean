// expect: 7:3 the first clause of a switch must be a case
interface Circle { readonly kind: 'circle'; readonly r: bigint; }
interface Square { readonly kind: 'square'; readonly side: bigint; }
interface Dot { readonly kind: 'dot'; }
type Shape = Circle | Square | Dot;
export function f(s: Shape): bigint {
  switch (s.kind) {
    default:
      return 0n;
  }
}
