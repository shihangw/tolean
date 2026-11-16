// expect: a sort condition depends on changing loop state
export function f(xs: ReadonlyArray<number>, flags: ReadonlyArray<boolean>): ReadonlyArray<number> {
  let values = xs;
  for (const flag of flags) {
    values = values.toSorted((a, b) => a - b);
    if (flag) { values = [...values, 0]; }
  }
  return values;
}
