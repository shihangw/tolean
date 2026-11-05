export interface Circle {
  readonly kind: 'circle';
  readonly r: bigint;
}

export interface Square {
  readonly kind: 'square';
  readonly side: bigint;
}

export type Shape = Circle | Square;

export function area(s: Shape): bigint {
  if (s.kind === 'circle') {
    return 3n * s.r * s.r;
  }
  return s.side * s.side;
}

export function unit(round: boolean): Shape {
  if (round) {
    return { kind: 'circle', r: 1n };
  }
  return { kind: 'square', side: 1n };
}

export function total(shapes: ReadonlyArray<Shape>): bigint {
  let sum = 0n;
  for (const s of shapes) {
    if ('square' !== s.kind) {
      sum += s.r;
    } else {
      sum += s.side;
    }
  }
  return sum;
}

interface Start {
  readonly type: 'start';
  readonly origin: bigint;
}

interface Stop {
  readonly type: 'stop';
}

interface Move {
  readonly type: 'move';
  readonly delta: bigint;
}

type Event = Start | Stop | Move;

export function position(e: Event, now: bigint): bigint {
  if (e.type === 'start') return e.origin;
  if (e.type === 'stop') return now;
  return now + e.delta;
}

export function maybeArea(s: Shape | null): bigint {
  if (s === null) return 0n;
  return area(s);
}
