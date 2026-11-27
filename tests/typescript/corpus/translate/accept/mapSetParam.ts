export function f(m: Map<string, bigint>): bigint {
  m.set('a', 1n);
  return 0n;
}
