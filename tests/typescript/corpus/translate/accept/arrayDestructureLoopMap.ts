// A map gives each entry as `[key, value]`, so `for (const [k, v] of m)`
// names both parts.
export function total(m: Map<string, bigint>): bigint {
  let sum = 0n;
  for (const [, v] of m) {
    sum += v;
  }
  return sum;
}

export function longKeys(m: Map<string, bigint>): bigint {
  let count = 0n;
  for (const [k, v] of m) {
    if (k.length > 2 && v > 0n) {
      count += 1n;
    }
  }
  return count;
}
