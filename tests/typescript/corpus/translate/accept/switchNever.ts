interface Circle {
  readonly kind: 'circle';
  readonly r: bigint;
}

interface Square {
  readonly kind: 'square';
  readonly side: bigint;
}

interface Dot {
  readonly kind: 'dot';
}

export type Shape = Circle | Square | Dot;

// A default that assigns the value to never checks that the cases cover every
// member. It never runs, so the output leaves it out.
export function size(s: Shape): bigint {
  switch (s.kind) {
    case 'circle':
      return s.r;
    case 'square':
      return s.side;
    case 'dot':
      return 0n;
    default: {
      const unreachable: never = s;
      return unreachable;
    }
  }
}

// The statements after the check never run either, so they may return
// anything.
export function corners(s: Shape, fallback: bigint): bigint {
  switch (s.kind) {
    case 'square':
      return 4n;
    case 'circle':
    {
      return 0n;
    }
    case 'dot':
      return 0n;
    default: {
      const _exhaustive: never = (s);
      return fallback;
    }
  }
}

// In a switch whose clauses end in break, the last case needs its break, or
// it would run into the default.
export function area(shapes: ReadonlyArray<Shape>): bigint {
  let total = 0n;
  for (const s of shapes) {
    switch (s.kind) {
      case 'circle':
        total += 3n * s.r * s.r;
        break;
      case 'square':
        total += s.side * s.side;
        break;
      case 'dot':
        break;
      default: {
        const _check: never = s;
      }
    }
  }
  return total;
}
