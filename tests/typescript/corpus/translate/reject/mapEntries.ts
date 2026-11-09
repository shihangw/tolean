// expect: 3:18 the entries do not have the key and value types of the map
export function f(): Map<string, bigint> {
  return new Map(new Set<string>());
}
