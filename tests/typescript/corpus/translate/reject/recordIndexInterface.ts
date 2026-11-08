// expect: 6:10 only a value of a Record type
interface Point {
  readonly x: bigint;
}
export function f(p: Point): bigint {
  return p['x'];
}
