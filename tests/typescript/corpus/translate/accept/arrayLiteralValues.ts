interface Point {
  readonly x: bigint;
  readonly y: bigint;
}
function total(xs: ReadonlyArray<bigint>): bigint {
  let s = 0n;
  for (const x of xs) {
    s += x;
  }
  return s;
}
export function pair(a: bigint, b: bigint): ReadonlyArray<bigint> {
  return [a, b];
}
export function sumOfThree(a: bigint): bigint {
  return total([a, a + 1n, 2n]);
}
export function maybe(x: bigint | null): ReadonlyArray<bigint | null> {
  return [x, null, 0n];
}
export function corners(p: Point): ReadonlyArray<Point> {
  return [p, { x: p.y, y: p.x }];
}
export function grid(): ReadonlyArray<ReadonlyArray<bigint>> {
  return [[1n, 2n], [], [3n]];
}
