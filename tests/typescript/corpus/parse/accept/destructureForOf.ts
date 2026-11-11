// A `for … of` loop may take each value apart with an array pattern, as a
// `const [..] = e` statement does.
export function f(m: ReadonlyMap<string, bigint>, rows: ReadonlyArray<[bigint, bigint, bigint]>) {
  let total = 0n;
  for (const [k, v] of m) {
    total += v;
  }
  for (let [, b] of rows) b;
  for (const [a, , c] of rows) {
    total += a + c;
  }
  for (const [first, ...others] of rows) {
    if (others.length > 0) continue;
    total += first;
  }
  for (const [...all] of rows.filter((r) => r[0] > 0n)) {
    total += all[0];
  }
  return total;
}
