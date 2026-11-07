// expect: 5:22 'Point' takes no type arguments
interface Point {
  readonly x: bigint;
}
export function f(p: Point<bigint>): bigint {
  return p.x;
}
