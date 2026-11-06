// expect: 8:10 'hexagon' is not the tag of a member of the union
interface Circle { readonly kind: 'circle'; readonly r: bigint; }
interface Square { readonly kind: 'square'; readonly side: bigint; }
interface Dot { readonly kind: 'dot'; }
type Shape = Circle | Square | Dot;
export function f(s: Shape): bigint {
  switch (s.kind) {
    case 'hexagon':
      return 6n;
  }
  return 0n;
}
