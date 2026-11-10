// expect: 2:1 a function may call itself only on a part of one of its parameters, the same one in every call
export function recurse(n?: bigint): bigint {
  if (n === undefined) return 0n;
  const again: bigint | null = n;
  if (again === null) return 0n;
  return recurse(again);
}
