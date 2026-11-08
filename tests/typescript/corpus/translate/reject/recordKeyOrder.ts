// expect: 5:10 order
type Kind = 'a' | 'b';
type Counts = Record<Kind, bigint>;
export function f(): Counts {
  return { b: 1n, a: 2n };
}
