type Level = 'low' | 'high';

export function levels(): Map<Level, bigint> {
  return new Map<Level, bigint>([['low', 1n], ['high', 10n], ['low', 2n]]);
}

export function copy(m: ReadonlyMap<string, bigint>): Map<string, bigint> {
  const c = new Map(m);
  c.set('extra', 0n);
  return c;
}

export function fromPairs(ps: ReadonlyArray<[string, boolean]>): number {
  return new Map(ps).size;
}

export function unique(xs: ReadonlyArray<bigint>): number {
  return new Set(xs).size;
}

export function tags(): Set<string> {
  const s: Set<string> = new Set(['a', 'b', 'a']);
  s.add('c');
  return s;
}
