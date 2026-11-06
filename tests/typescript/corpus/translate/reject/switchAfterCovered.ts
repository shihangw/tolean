// expect: 7:3 code after a switch whose cases cover every member is unreachable
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
    case 'dot':
      return 3n;
  }
  return 0n;
}
