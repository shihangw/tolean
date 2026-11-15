// expect: 5:14 the key must have the key type of the Record
type K = 'a' | 'b';
type R = Record<K, bigint>;
export function f(r: R | null, k: string): bigint {
  return r?.[k] ?? 0n;
}
