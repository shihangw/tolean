// expect: 3:16 the key does not have the map's key type
export function f(m: ReadonlyMap<string, bigint>): bigint {
  return m.get(1n) ?? 0n;
}
