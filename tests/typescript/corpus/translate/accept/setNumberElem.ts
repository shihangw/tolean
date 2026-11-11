/** The number of distinct values. A set holds at most one `NaN`, and `0` and
 * `-0` are one element. */
export function distinct(xs: ReadonlyArray<number>): number {
  return new Set<number>(xs).size;
}

export function withoutNaN(xs: ReadonlyArray<number>): Set<number> {
  const s = new Set<number>();
  for (const x of xs) {
    s.add(x);
  }
  s.delete(NaN);
  return s;
}

export function hasZero(s: ReadonlySet<number>): boolean {
  return s.has(0) || s.has(-0);
}
