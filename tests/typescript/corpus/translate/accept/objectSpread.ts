// `{ ...a, f: e }`, where `a` has the interface of the result, becomes
// `{ a with f := e }`. The spread keeps the keys of `a` in their order, and a
// property after it sets a field in its place.
export interface Point {
  readonly x: bigint;
  readonly y: bigint;
  readonly label: string;
}

export function moveRight(p: Point, by_: bigint): Point {
  return { ...p, x: p.x + by_ };
}

export function rename(p: Point, label: string): Point {
  return { ...p, label };
}

export function swap(p: Point): Point {
  return { ...p, y: p.x, x: p.y };
}

export function copy(p: Point): Point {
  return { ...p };
}

export function reset(ps: ReadonlyArray<Point>): ReadonlyArray<Point> {
  return ps.map((p) => ({ ...p, x: 0n, y: 0n }));
}

export function shifted(p: Point): bigint {
  const q = { ...p, y: p.y + 1n };
  return q.y;
}
