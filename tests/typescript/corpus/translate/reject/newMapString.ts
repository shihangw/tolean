// expect: 3:34 the entries do not have the key and value types of the map
export function f(s: string): Map<string, string> {
  return new Map<string, string>(s);
}
