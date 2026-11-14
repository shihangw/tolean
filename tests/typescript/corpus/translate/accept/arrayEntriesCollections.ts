// `new Map(xs.entries())` keys each element by its index. On a map,
// `m.entries()` gives the entries, as a loop over the map does.
export function byIndex(xs: ReadonlyArray<string>): Map<number, string> {
  return new Map(xs.entries());
}

export function valueSum(m: ReadonlyMap<string, bigint>): bigint {
  let total = 0n;
  for (const [, v] of m.entries()) {
    total = total + v;
  }
  return total;
}
