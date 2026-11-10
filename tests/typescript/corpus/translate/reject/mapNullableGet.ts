// expect: 3:10 get on a map of nullable values is not supported
export function f(m: ReadonlyMap<string, bigint | null>): boolean {
  return m.get('a') === undefined;
}
