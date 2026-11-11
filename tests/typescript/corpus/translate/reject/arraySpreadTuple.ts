// expect: 3:11 a spread '...' may only be an element of an array literal
export function pair(xs: ReadonlyArray<bigint>): readonly [bigint, bigint] {
  return [...xs, 0n];
}
