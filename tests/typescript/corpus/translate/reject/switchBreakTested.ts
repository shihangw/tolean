// expect: 8:3 the local that a switch tests may not be assigned in its clauses
interface Circle { readonly kind: 'circle'; readonly r: bigint; }
interface Square { readonly kind: 'square'; readonly side: bigint; }
interface Dot { readonly kind: 'dot'; }
type Shape = Circle | Square | Dot;
export function f(s: Shape, t: Shape): bigint {
  let u = s;
  switch (u.kind) {
    case 'circle':
      u = t;
      break;
  }
  return 0n;
}
