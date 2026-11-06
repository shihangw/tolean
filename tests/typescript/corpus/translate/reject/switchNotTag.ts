// expect: 7:11 a switch must test the tag of a local of a tagged union
interface Circle { readonly kind: 'circle'; readonly r: bigint; }
interface Square { readonly kind: 'square'; readonly side: bigint; }
interface Dot { readonly kind: 'dot'; }
type Shape = Circle | Square | Dot;
export function f(n: bigint): bigint {
  switch (n) {
    case 1n:
      return 1n;
    default:
      return 0n;
  }
}
