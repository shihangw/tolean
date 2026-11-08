// expect: 7:3 the cases before this clause cover every member, so it never runs
interface Circle { readonly kind: 'circle'; readonly r: bigint; }
interface Square { readonly kind: 'square'; readonly side: bigint; }
interface Dot { readonly kind: 'dot'; }
type Shape = Circle | Square | Dot;
export function f(s: Shape, t: Shape): bigint {
  switch (s.kind) {
    case 'circle':
      return 1n;
    case 'square':
      return 2n;
    case 'dot':
      return 3n;
    default: {
      const unreachable: never = t;
      return unreachable;
    }
  }
}
