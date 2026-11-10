// expect: 2:1 a function may call itself only on a part of one of its parameters, the same one in every call
export function recurse(n: bigint): bigint {
  const wrapped: bigint | null = n;
  if (wrapped === null) return 0n;
  return recurse(wrapped);
}
