// expect: 3:10 new Map takes no entries here
export function f(): Map<string, bigint> {
  return new Map<string, bigint>([['a', 1n]]);
}
