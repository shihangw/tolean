// expect: 10:10 an earlier case of the switch already takes 'circle'
interface Circle { readonly kind: 'circle'; readonly r: bigint; }
interface Square { readonly kind: 'square'; readonly side: bigint; }
interface Dot { readonly kind: 'dot'; }
type Shape = Circle | Square | Dot;
export function f(s: Shape): bigint {
  switch (s.kind) {
    case 'circle':
      return 1n;
    case 'circle':
      return 2n;
  }
  return 0n;
}
