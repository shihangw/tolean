// expect: 3:22 is reserved in Lean, so it cannot name a field of the Record
type Kind = 'open' | 'def';
type Counts = Record<Kind, bigint>;
export function f(c: Counts): bigint {
  return c.open;
}
