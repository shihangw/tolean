// expect: 5:40 type guards are not supported
interface Circle { readonly kind: "circle"; readonly radius: bigint; }
interface Square { readonly kind: "square"; readonly side: bigint; }
type Shape = Circle | Square;
function isCircle(shape: Shape): shape is Circle {
  return shape.kind === "circle";
}
