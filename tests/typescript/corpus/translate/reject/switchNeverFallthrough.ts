// expect: 8:3 every clause of a switch must end in a return, or every clause in a break
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
      break;
    case 'dot':
      n = 2n;
    default: {
      const unreachable: never = s;
    }
  }
  return n;
}
