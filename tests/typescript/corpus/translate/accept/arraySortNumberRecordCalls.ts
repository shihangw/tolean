// certify: required
interface Box { readonly values: ReadonlyArray<number>; }
interface Outer { readonly payload: Box; }
function sorted(xs: ReadonlyArray<number>): number[] {
  return xs.toSorted((a, b) => a - b);
}
export function record(xs: ReadonlyArray<number>): Box {
  return { values: sorted(xs) };
}
export function updated(box: Box, xs: ReadonlyArray<number>): Box {
  return { ...box, values: sorted([...xs, 0]) };
}
export function nested(xs: ReadonlyArray<number>): Outer {
  return { payload: { values: sorted(xs) } };
}
export function mapped(boxes: ReadonlyArray<Box>): Box[] {
  return boxes.map(box => ({ values: sorted([...box.values, 0]) }));
}
export function collected(boxes: ReadonlyArray<Box>): ReadonlyArray<Box> {
  let result: ReadonlyArray<Box> = [];
  for (const box of boxes) {
    result = [...result, { values: sorted(box.values) }];
  }
  return result;
}
