interface Point {
  readonly x: bigint;
  readonly y: bigint;
}

// An optional parameter is undefined when a call leaves it out.
export function scale(p: Point, factor?: bigint): Point {
  return { x: p.x * (factor ?? 1n), y: p.y * (factor ?? 1n) };
}

// A call may leave out an optional parameter, pass a value, pass undefined,
// or pass on an optional value of its own.
export function grow(p: Point, factor?: bigint): Point {
  const a = scale(p);
  const b = scale(a, 2n);
  const c = scale(b, undefined);
  return scale(c, factor);
}

// A test of undefined narrows the parameter, as a test of null does.
export function offset(p: Point, dx?: bigint, dy?: bigint): Point {
  if (dx === undefined) {
    return p;
  }
  let y = p.y;
  if (dy !== undefined) {
    y = y + dy;
  }
  return { x: p.x + dx, y: y };
}

export function next(n?: number): number {
  if (undefined !== n) {
    return n + 1;
  }
  return 0;
}

// `?.` on an optional parameter of an interface type.
export function xOr(p?: Point): bigint {
  return p?.x ?? 0n;
}

export function isSet(flag?: boolean): boolean {
  return flag !== undefined;
}
