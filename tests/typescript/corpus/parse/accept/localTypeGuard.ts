interface Circle { readonly kind: "circle"; readonly radius: bigint; }
interface Square { readonly kind: "square"; readonly side: bigint; }
type Shape = Circle | Square;
function area(shape: Shape): bigint {
  function isCircle(value: Shape): value is Circle {
    return value.kind === "circle";
  }
  if (isCircle(shape)) { return shape.radius * shape.radius; }
  return shape.side * shape.side;
}
function localArrow(shape: Shape): boolean {
  const isCircle = (value: Shape): value is Circle => {
    return value.kind === "circle";
  };
  return isCircle(shape);
}
