interface Box<T> {
  readonly value: T;
}

export interface Pair<A, B> {
  readonly first: A;
  readonly second: B;
}

type Maybe<T> = T | null;

export type Entry<K, V> = readonly [K, V];
