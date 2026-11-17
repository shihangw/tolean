// expect: 2:22 Record<string, V> is not supported yet: dynamic string lookup needs a certificate condition for inherited Object.prototype properties; naming the Record does not remove this requirement
type Totals = Record<string, bigint>;
export function f(t: Totals): bigint {
  return 0n;
}
