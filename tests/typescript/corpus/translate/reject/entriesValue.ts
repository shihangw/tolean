// expect: 5:14 the array method 'entries' is not supported here
// An iterator is used up by one loop, so the subset reads xs.entries() only
// where a loop, a spread or new Map uses it at once.
export function f(xs: ReadonlyArray<bigint>): bigint {
  const it = xs.entries();
  let total = 0n;
  for (const [, x] of it) {
    total = total + x;
  }
  return total;
}
