type U = string | bigint;

export function f(n: number): bigint {
  const u: U = 1n;
  if (typeof u === 'string') return 0n;
  return u;
}
