// expect: 5:34 a type guard must be true exactly on its annotated type
interface Circle { readonly kind: "circle"; readonly radius: bigint; }
interface Square { readonly kind: "square"; readonly side: bigint; }
type Shape = Circle | Square;
function isCircle(shape: Shape): shape is Circle {
  return shape.kind === "square";
}
