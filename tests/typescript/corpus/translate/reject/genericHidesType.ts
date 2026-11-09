// expect: 5:1 the type parameter 'Point' would hide the type or function Point in Lean; choose another name
interface Point {
  readonly x: bigint;
}
export function f<Point>(p: Point): Point {
  return p;
}
