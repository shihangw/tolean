interface Point {
  readonly x: bigint;
  readonly y: bigint;
}

export function identity<T>(x: T): T {
  return x;
}

export function pair<A, B>(a: A, b: B): [A, B] {
  return [a, b];
}

export function swap<A, B>(p: [A, B]): [B, A] {
  return [p[1], p[0]];
}

// A generic function may call another one.
export function twice<T>(x: T): [T, T] {
  return pair(x, x);
}

export function orElse<T>(x: T | null, fallback: T): T {
  return x ?? fallback;
}

export function count<T>(xs: T[]): bigint {
  let n = 0n;
  for (const x of xs) {
    n += 1n;
  }
  return n;
}

export function samePoint(p: Point): Point {
  return identity(p);
}

export function second(a: bigint, b: string): bigint {
  return swap(pair(a, b))[1];
}

// `null` leaves the type parameter to the other argument.
export function orZero(n: bigint | null): bigint {
  return orElse(n, 0n) + orElse(null, 1n);
}

export function countNames(names: string[]): bigint {
  return count(names) + count([true, false]);
}

// A tuple literal keeps its shape where a generic tuple is expected, and its
// elements fix the type parameters.
export function swapped(): [string, bigint] {
  return swap([1n, 'x']);
}

// An element that the context's type parameter allows keeps that type.
export function maybeFirst<T>(x: T): [T | null, T] {
  return [null, x];
}
