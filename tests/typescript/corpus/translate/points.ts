interface Point {
  readonly x: bigint;
  readonly y: bigint;
}

function add(a: Point, b: Point): Point {
  return { x: a.x + b.x, y: a.y + b.y };
}

function sumFrom(points: ReadonlyArray<Point>, start: Point): Point {
  let total = start;
  for (const p of points) {
    total = add(total, p);
  }
  return total;
}

export function sum(points: ReadonlyArray<Point>, origin: Point | null): Point {
  if (origin === null) {
    return sumFrom(points, { x: 0n, y: 0n });
  }
  return sumFrom(points, origin);
}

export function farthest(points: ReadonlyArray<Point>): bigint {
  let best = -1n;
  for (const p of points) {
    const d = p.x * p.x + p.y * p.y;
    if (d > best) {
      best = d;
    }
  }
  return best;
}
