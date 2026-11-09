// expect: 7:3 the field 'Point' before this one would hide the type Point in Lean; rename the field
interface Point {
  readonly x: bigint;
}
interface Pair {
  readonly Point: bigint;
  readonly p: Point;
}

export function origin(): Pair {
  return { Point: 0n, p: { x: 0n } };
}
