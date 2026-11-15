// expect: 10:16 the argument does not have the parameter's type
interface Circle { readonly kind: "circle"; readonly radius: bigint; }
interface Square { readonly kind: "square"; readonly side: bigint; }
type Shape = Circle | Square;
interface OtherCircle { readonly kind: "circle"; readonly a: bigint; }
interface OtherSquare { readonly kind: "square"; readonly b: bigint; }
type Other = OtherCircle | OtherSquare;
function isCircle(shape: Shape): shape is Circle { return shape.kind === "circle"; }
export function wrong(value: Other): boolean {
  if (isCircle(value)) { return true; } else { return false; }
}
