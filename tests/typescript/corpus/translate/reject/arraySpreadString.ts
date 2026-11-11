// expect: 3:11 a spread '...' in an array needs an array, a set or a map
export function chars(s: string): ReadonlyArray<string> {
  return [...s];
}
