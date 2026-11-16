// certify: required
interface Box { readonly values: ReadonlyArray<number>; }
function sorted(xs: ReadonlyArray<number>): number[] {
  return xs.toSorted((a, b) => a - b);
}
export function expression(box: Box | null): boolean {
  return box === null || sorted(box.values).length > 0;
}
export function statement(box: Box | null): ReadonlyArray<number> {
  if (box === null) { return []; }
  return sorted(box.values);
}
export function fallback(box: Box | null, xs: ReadonlyArray<number>): ReadonlyArray<number> {
  if (box === null) { return sorted(xs); }
  return sorted(box.values);
}
export function nested(a: Box | null, b: Box | null): ReadonlyArray<number> {
  if (a === null) { return []; }
  if (b === null) { return sorted(a.values); }
  return sorted([...a.values, ...b.values]);
}
export function mapped(boxes: ReadonlyArray<Box | null>): boolean[] {
  return boxes.map(box => box === null || sorted(box.values).length > 0);
}
export function filtered(boxes: ReadonlyArray<Box | null>): ReadonlyArray<Box | null> {
  return boxes.filter(box => box !== null && sorted(box.values).length > 0);
}
export function collected(boxes: ReadonlyArray<Box | null>): ReadonlyArray<number> {
  let result: ReadonlyArray<number> = [];
  for (const box of boxes) {
    if (box !== null) {
      result = [...result, ...sorted(box.values)];
    }
  }
  return result;
}
export function optional(xs?: ReadonlyArray<number>): boolean {
  if (xs === undefined) { return false; }
  return sorted(xs).length > 0;
}
export function undefinedGuard(box: Box | undefined): number[] {
  return box === undefined ? [] : sorted(box.values);
}
export function forwarded(box: Box | null): boolean {
  return expression(box);
}
export function shadowed(some: Box | null, True: ReadonlyArray<number>): ReadonlyArray<number> {
  if (some === null) { return sorted(True); }
  return sorted(some.values);
}
