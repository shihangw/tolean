export interface Branch<T> {
  readonly value: T;
  readonly next?: Branch<T>;
}

export function depth<T>(n?: Branch<T>): bigint {
  if (n === undefined) return 0n;
  return 1n + depth(n.next);
}
