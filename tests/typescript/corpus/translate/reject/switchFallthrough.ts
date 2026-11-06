// expect: 8:10 every clause of a switch must end in a return
interface Circle { readonly kind: 'circle'; readonly r: bigint; }
interface Square { readonly kind: 'square'; readonly side: bigint; }
interface Dot { readonly kind: 'dot'; }
type Shape = Circle | Square | Dot;
export function f(s: Shape): bigint {
  switch (s.kind) {
    case 'circle':
    case 'square':
      return 1n;
    default:
      return 0n;
  }
}
