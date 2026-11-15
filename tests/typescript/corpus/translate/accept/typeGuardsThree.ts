interface Circle { readonly kind: "circle"; readonly radius: bigint; }
interface Square { readonly kind: "square"; readonly side: bigint; }
interface Triangle { readonly kind: "triangle"; readonly height: bigint; }
type Shape = Circle | Square | Triangle;

function isCircle(shape: Shape): shape is Circle { return shape.kind === "circle"; }
function isSquare(shape: Shape): shape is Square {
  if (shape.kind === "square") { return true; } else { return false; }
}

export function size(shape: Shape): bigint {
  if (isCircle(shape)) { return shape.radius; }
  else if (isSquare(shape)) { return shape.side; }
  else { return shape.height; }
}
