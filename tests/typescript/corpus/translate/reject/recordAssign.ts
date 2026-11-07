// expect: 5:3 assign
type Kind = 'a' | 'b';
type Counts = Record<Kind, bigint>;
export function f(c: Counts, k: Kind): bigint {
  c[k] = 1n;
  return c.a;
}
