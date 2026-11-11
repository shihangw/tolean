// expect: 3:10 an index of an array of nullable values could give null or undefined
export function f(xs: ReadonlyArray<bigint | null>): bigint {
  return xs[0] ?? 0n;
}
