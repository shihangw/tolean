// certify: required
interface Box { readonly values: ReadonlyArray<number>; }
function sorted(xs: ReadonlyArray<number>): number[] {
  return xs.toSorted((a, b) => a - b);
}
export function wrapped(xs: ReadonlyArray<number>): Box {
  return { values: sorted(xs) };
}
export function replacement(box: Box, xs: ReadonlyArray<number>): Box {
  return { ...box, values: sorted(xs) };
}
export function wrappedBase(xs: ReadonlyArray<number>): Box {
  return { ...wrapped(xs), values: xs };
}
export function wrappedBoth(xs: ReadonlyArray<number>, ys: ReadonlyArray<number>): Box {
  return { ...wrapped(xs), values: sorted(ys) };
}
