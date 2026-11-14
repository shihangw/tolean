// expect: 5:45 type guards are not supported
interface Circle { readonly kind: "circle"; readonly radius: bigint; }
interface Square { readonly kind: "square"; readonly side: bigint; }
type Shape = Circle | Square;
function isLargeCircle(shape: Shape): shape is Circle {
  if (shape.kind === "circle") { return shape.radius > 0n; }
  return false;
}
export function size(shape: Shape): bigint {
  if (isLargeCircle(shape)) { return shape.radius; }
  // A circle with radius zero reaches this branch too.
  return shape.side;
}
