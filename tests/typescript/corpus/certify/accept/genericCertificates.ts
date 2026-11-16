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
