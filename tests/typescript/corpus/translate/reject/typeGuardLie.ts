// expect: 5:34 a type guard must have one required parameter and return exactly a strict test of its tag
interface Circle { readonly kind: "circle"; readonly radius: bigint; }
interface Square { readonly kind: "square"; readonly side: bigint; }
type Shape = Circle | Square;
function isCircle(shape: Shape): shape is Circle {
  return true;
}
export function size(shape: Shape): bigint {
  if (isCircle(shape)) { return shape.radius; }
  return shape.side;
}
