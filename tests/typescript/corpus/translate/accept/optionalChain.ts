// `x?.f` is `undefined` when `x` is null or undefined, and `x.f` otherwise.
export interface Point {
  readonly x: bigint;
  readonly label?: string;
}

export function xOr(p: Point | null, d: bigint): bigint {
  return p?.x ?? d;
}

export function hasLabel(p: Point | null): boolean {
  return p?.label !== undefined;
}

export function labelOr(p: Point | null): string {
  return p?.label ?? 'none';
}

export interface Segment {
  readonly start: Point;
  readonly stop?: Point;
}

export function endX(s: Segment): bigint {
  return s.stop?.x ?? s.start.x;
}

export function xOrZero(p: Point | null): bigint {
  const x = p?.x;
  return x ?? 0n;
}
