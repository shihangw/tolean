// expect: 3:11 the spread's elements do not have the array's element type
export function widen(xs: ReadonlyArray<bigint>): ReadonlyArray<bigint | null> {
  return [...xs, null];
}
