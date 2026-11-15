// expect: 7:3 'isCircle' would hide the function or global
interface Circle { readonly kind: "circle"; readonly radius: bigint; }
interface Square { readonly kind: "square"; readonly side: bigint; }
type Shape = Circle | Square;
function isCircle(shape: Shape): shape is Circle { return shape.kind === "circle"; }
export function shadow(shape: Shape): boolean {
  function isCircle(value: Shape): boolean { return false; }
  if (isCircle(shape)) { return true; } else { return false; }
}
