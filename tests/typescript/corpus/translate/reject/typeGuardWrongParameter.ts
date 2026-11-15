// expect: 5:48 a type guard must have one required parameter and return exactly a strict test of its tag
interface Circle { readonly kind: "circle"; readonly radius: bigint; }
interface Square { readonly kind: "square"; readonly side: bigint; }
type Shape = Circle | Square;
function isCircle(shape: Shape, other: Shape): shape is Circle {
  return other.kind === "circle";
}
export function size(shape: Shape, other: Shape): bigint {
  if (isCircle(shape, other)) { return shape.radius; }
  return shape.side;
}
