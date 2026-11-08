// expect: 5:12 the key must have the key type of the Record
type Kind = 'a' | 'b';
type Counts = Record<Kind, bigint>;
export function f(c: Counts, s: string): bigint {
  return c[s];
}
