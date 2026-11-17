// expect: 6:28 indexed access to a single-literal tag field is not supported; use a named literal-union type
interface Shape {
  readonly kind: "circle";
  readonly size: bigint;
}
export function make(kind: Shape["kind"]): Shape {
  return { kind, size: 1n };
}
