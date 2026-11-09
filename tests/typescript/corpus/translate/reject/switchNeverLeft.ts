// expect: 7:3 's' is not never in this default, because no case takes 'dot'
interface Circle { readonly kind: 'circle'; readonly r: bigint; }
interface Square { readonly kind: 'square'; readonly side: bigint; }
interface Dot { readonly kind: 'dot'; }
type Shape = Circle | Square | Dot;
export function f(s: Shape): bigint {
  switch (s.kind) {
    case 'circle':
      return 1n;
    case 'square':
      return 2n;
    default: {
      const unreachable: never = s;
      return unreachable;
    }
  }
}
