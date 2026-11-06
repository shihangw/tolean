// expect: 8:3 a loop body may not return, break or continue
interface Circle { readonly kind: 'circle'; readonly r: bigint; }
interface Square { readonly kind: 'square'; readonly side: bigint; }
interface Dot { readonly kind: 'dot'; }
type Shape = Circle | Square | Dot;
export function f(shapes: ReadonlyArray<Shape>): bigint {
  let n = 0n;
  for (const s of shapes) {
    switch (s.kind) {
      case 'circle':
        n += 1n;
        break;
    }
  }
  return n;
}
