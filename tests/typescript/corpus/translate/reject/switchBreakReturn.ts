// expect: 12:10 a clause of a switch that ends in break may not return
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
    case 'square':
      return 2n;
  }
  return n;
}
