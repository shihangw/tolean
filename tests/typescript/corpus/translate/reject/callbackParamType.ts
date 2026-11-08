// expect: 3:18 the parameter must have the element type of the array
export function f(xs: ReadonlyArray<bigint>): ReadonlyArray<bigint> {
  return xs.map((x: boolean) => 1n);
}
