export function total(m: ReadonlyMap<string, bigint>): bigint {
  let sum = 0n;
  for (const e of m) {
    sum += e[1];
  }
  return sum;
}

export function longest(words: ReadonlyArray<string>): bigint {
  const counts = new Map<string, bigint>();
  for (const w of words) {
    counts.set(w, (counts.get(w) ?? 0n) + 1n);
  }
  let best = 0n;
  for (const e of counts) {
    if (e[1] > best) best = e[1];
  }
  return best;
}

export function count(s: ReadonlySet<bigint>): bigint {
  let n = 0n;
  for (const x of s) {
    n += x;
  }
  return n;
}
