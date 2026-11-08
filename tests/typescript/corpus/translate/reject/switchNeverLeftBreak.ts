// expect: 8:3 's' is not never in this default, because no case takes 'square'
interface Circle { readonly kind: 'circle'; readonly r: bigint; }
interface Square { readonly kind: 'square'; readonly side: bigint; }
interface Dot { readonly kind: 'dot'; }
type Shape = Circle | Square | Dot;
export function f(s: Shape): bigint {
  let n = 0n;
  switch (s.kind) {
    case 'circle':
      n = 1n;
      break;
    case 'dot':
      n = 2n;
      break;
    default: {
      const unreachable: never = s;
    }
  }
  return n;
}
