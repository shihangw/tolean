// expect: 9:12 a clause of a switch that ends in break may not return, break or continue before its end
interface Circle { readonly kind: 'circle'; readonly r: bigint }
interface Square { readonly kind: 'square'; readonly side: bigint }
type Shape = Circle | Square;
export function f(xs: ReadonlyArray<Shape>): bigint {
  let s = 0n;
  for (const x of xs) {
    switch (x.kind) {
      case 'circle':
        if (x.r > 3n) continue;
        s += x.r;
        break;
      case 'square':
        s += x.side;
        break;
    }
  }
  return s;
}
