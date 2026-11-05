// expect: 7:3 the default must be the last clause of a switch
interface Circle { readonly kind: 'circle'; readonly r: bigint; }
interface Square { readonly kind: 'square'; readonly side: bigint; }
interface Dot { readonly kind: 'dot'; }
type Shape = Circle | Square | Dot;
export function f(s: Shape): bigint {
  switch (s.kind) {
    case 'circle':
      return 1n;
    default:
      return 0n;
    case 'square':
      return 2n;
  }
}
