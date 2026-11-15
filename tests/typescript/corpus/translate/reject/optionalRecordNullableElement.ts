// expect: 5:10 an optional Record index could give null or undefined
type K = 'a' | 'b';
type R = Record<K, bigint | null>;
export function f(r: R | null, k: K): bigint {
  return r?.[k] ?? 0n;
}
