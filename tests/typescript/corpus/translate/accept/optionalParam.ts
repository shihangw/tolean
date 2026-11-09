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

// A value passed for a generic optional parameter fixes its type parameter.
function take<T>(x?: T): T | null {
  if (x === undefined) return null;
  return x;
}

export function takeOne(): bigint | null {
  return take(1n);
}

// `undefined` fixes nothing, so the other arguments fix the type parameter,
// before or after it.
function choose<T>(fallback: T, x?: T): T {
  return x ?? fallback;
}

export function chooseFallback(): bigint {
  return choose(1n, undefined);
}

function pick<T>(a: bigint, x?: T, y?: T): bigint {
  return a;
}

export function pickFirst(): bigint {
  return pick(1n, undefined, 2n);
}
