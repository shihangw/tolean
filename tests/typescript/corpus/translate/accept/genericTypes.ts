interface Box<T> {
  readonly value: T;
}

export interface Pair<A, B> {
  readonly first: A;
  readonly second: B;
}

type Maybe<T> = T | null;
type Twice<T> = [T, T];

export function box<T>(value: T): Box<T> {
  return { value };
}

export function unbox<T>(b: Box<T>): T {
  return b.value;
}

export function swapPair<A, B>(p: Pair<A, B>): Pair<B, A> {
  return { first: p.second, second: p.first };
}

export function orDefault<T>(x: Maybe<T>, fallback: T): T {
  return x ?? fallback;
}

export function twice<T>(x: T): Twice<T> {
  return [x, x];
}

export function boxedSum(a: Box<bigint>, b: Box<bigint>): bigint {
  return a.value + b.value;
}

// The arguments fix T, through a field of a generic interface too.
export function roundTrip(n: bigint): bigint {
  return unbox(box(n)) + boxedSum(box(1n), { value: 2n });
}

export function flip(p: Pair<string, bigint>): Pair<bigint, string> {
  return swapPair(p);
}

export function count(m: Maybe<bigint>): bigint {
  return orDefault(m, 0n) + twice(m ?? 1n)[0];
}
