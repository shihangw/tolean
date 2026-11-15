interface Circle { readonly kind: "circle"; readonly radius: bigint; }
interface Square { readonly kind: "square"; readonly side: bigint; }
type Shape = Circle | Square;

export function isCircle(shape: Shape): shape is Circle {
  return shape.kind === "circle";
}

export function isSquare(shape: Shape): shape is Square {
  return "circle" !== shape.kind;
}

export function size(shape: Shape): bigint {
  if (isCircle(shape)) { return shape.radius; }
  return shape.side;
}

export function squareSize(shape: Shape): bigint {
  if (isSquare(shape)) { return shape.side; } else { return shape.radius; }
}

export function circleValue(shape: Shape): boolean {
  return isCircle(shape);
}

export function aliasSize(shape: Shape): bigint {
  const alias = shape;
  if (isCircle(alias)) { return alias.radius; } else { return alias.side; }
}

type Mixed = string | bigint;
export function isText(value: Mixed): value is string {
  return typeof value === "string";
}

export function text(value: Mixed): string {
  if (isText(value)) { return value; } else { return "other"; }
}
