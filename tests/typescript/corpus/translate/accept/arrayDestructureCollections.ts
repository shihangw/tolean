// A pattern iterates a set or a map as `for … of` does: a set gives its
// elements and a map its entries `[key, value]`, in the order of insertion.
export function first(s: Set<string>): string {
  const [x] = s;
  return x ?? '';
}

export function firstTwo(s: Set<bigint>): bigint {
  const [a, b] = s;
  return (a ?? 0n) + (b ?? 0n);
}

export function laterEntries(m: Map<string, bigint>): number {
  const [, ...later] = m;
  return later.length;
}
