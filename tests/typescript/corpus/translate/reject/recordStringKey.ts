// expect: 2:22 the keys of a Record must be a literal union of strings
type Totals = Record<string, bigint>;
export function f(t: Totals): bigint {
  return 0n;
}
