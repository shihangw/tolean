// certify: required
type Maybe<T> = T | null;

export interface Box<T> {
  readonly value: T;
  extra?: Maybe<T>;
}

type OptionalGeneric<T> = {
  value?: T | null;
};

export function identity<T>(value: T): T {
  return value;
}

export function pair<A, B>(a: A, b: B): [A, B] {
  return [a, b];
}

export function box<T>(value: T): Box<T> {
  return { value };
}

export function unbox<T>(box: Box<T>): T {
  return box.value;
}

export function choose<T>(value: T | null, fallback: T): T {
  return value ?? fallback;
}

export function isNull<T>(value?: T | null): boolean {
  return value === null;
}

export function count<T>(values: ReadonlyArray<T>): bigint {
  let result = 0n;
  for (const value of values) {
    result += 1n;
  }
  return result;
}

export interface CollisionBox<T, T_, T__> {
  readonly first: T;
  readonly second: T_;
  readonly third: T__;
  readonly toleanCodec_T: bigint;
  readonly toleanCodec_T_: bigint;
}

export function collisionPair<T, T_>(a: T, b: T_, toleanCodec_T: bigint): [T, T_] {
  return [a, b];
}

export function collisionBox<T, T_, T__>(
  a: T, b: T_, c: T__, toleanCodec_T: bigint, toleanCodec_T_: bigint,
): CollisionBox<T, T_, T__> {
  return { first: a, second: b, third: c, toleanCodec_T, toleanCodec_T_ };
}

export function collisionUnbox<T, T_, T__>(box: CollisionBox<T, T_, T__>): [T, T_, T__] {
  return [box.first, box.second, box.third];
}
