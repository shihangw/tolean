type U = string | bigint;

export function f(c: boolean, n: number): bigint {
  const u: U = c ? 1n : 'a';
  if (typeof u === 'string') return 0n;
  return u;
}
