// expect: sort conditions across an enclosing nullable narrowing need scope propagation
export function f(xs: ReadonlyArray<number> | null): ReadonlyArray<number> {
  if (xs === null) { return []; }
  return xs.toSorted((a, b) => a - b);
}
