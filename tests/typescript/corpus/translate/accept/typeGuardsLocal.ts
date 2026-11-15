interface Circle { readonly kind: "circle"; readonly radius: bigint; }
interface Square { readonly kind: "square"; readonly side: bigint; }
type Shape = Circle | Square;

export function localSize(shape: Shape): bigint {
  function localCircle(value: Shape): value is Circle { return value.kind === "circle"; }
  if (localCircle(shape)) { return shape.radius; } else { return shape.side; }
}

export function arrowSize(shape: Shape): bigint {
  const localCircle = (value: Shape): value is Circle => { return value.kind === "circle"; };
  if (localCircle(shape)) { return shape.radius; } else { return shape.side; }
}
