// certify: required
type K = 'a' | 'b';
type R = Record<K, bigint>;
export function f(absent: boolean, r: R, k: K): bigint {
  return (absent ? null : r)?.[k] ?? 0n;
}
