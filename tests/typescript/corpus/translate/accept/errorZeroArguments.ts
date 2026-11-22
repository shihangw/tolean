class Empty extends Error {}

export function empty(n: number): number {
  if (n < 0) throw new Empty();
  return n;
}
