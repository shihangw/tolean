export interface Circle {
  readonly kind: 'circle';
  readonly r: bigint;
}

export interface Square {
  readonly kind: 'square';
  readonly side: bigint;
}

export interface Triangle {
  readonly kind: 'triangle';
  readonly base: bigint;
  readonly height: bigint;
}

export type Shape = Circle | Square | Triangle;

// Every member has a case, so Lean sees that the arms cover the union.
export function area(s: Shape): bigint {
  switch (s.kind) {
    case 'circle':
      return 3n * s.r * s.r;
    case 'square':
      return s.side * s.side;
    case 'triangle':
      return (s.base * s.height) / 2n;
  }
}

// A default takes the members that no case names.
export function corners(s: Shape): bigint {
  switch (s.kind) {
    case 'square': {
      const n = 4n;
      return n;
    }
    default:
      return 0n;
  }
}

// After the switch, the code runs for the members that no case names.
export function width(s: Shape): bigint {
  switch (s.kind) {
    case 'circle':
      return 2n * s.r;
    case 'square':
      return s.side;
  }
  return s.base;
}

interface Start {
  readonly type: 'start';
  readonly time: bigint;
}

interface Stop {
  readonly type: 'stop';
}

type Event = Start | Stop;

export function time(e: Event, now: bigint): bigint {
  switch (e.type) {
    case 'stop':
      return now;
    default:
      return e.time;
  }
}

// A loop inside a case: the certificate finds it in the clause.
export function sides(s: Shape, xs: ReadonlyArray<bigint>): bigint {
  switch (s.kind) {
    case 'square': {
      let n = 0n;
      for (const x of xs) {
        n += x;
      }
      return n;
    }
    default:
      return 0n;
  }
}
